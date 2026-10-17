import Goose.Lower.Validation.CfgEntryTargets

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem entry_newBlock_run (types : List VTy) (env : LEnv) (state : LS) :
    newBlock types env state =
      ((state.blocks.size, (List.range types.length).map (state.vals.size + ·)),
        { state with
          blocks := state.blocks.push ⟨((List.range types.length).map (state.vals.size + ·)).zip types, #[]⟩
          vals := types.foldl (fun values ty => values.push (some ty)) state.vals }) := rfl

def LoopEntryTargets (loop : Option LoopCtx) : Prop :=
  match loop with
  | none => True
  | some context => context.breakTo ≠ 0 ∧
      match context.cont with
      | .jump header | .next header _ _ => header ≠ 0

def EntryRun (loop : Option LoopCtx) (action : B α) : Prop :=
  ∀ env before result after, action env before = (result, after) →
    EntryTargets before → LoopEntryTargets loop →
    EntryTargets after ∧ LoopEntryTargets loop

theorem EntryRun.bind {loop : Option LoopCtx} {first : B α} {next : α → B β}
    (one : EntryRun loop first) (two : ∀ value, EntryRun loop (next value)) :
    EntryRun loop (first >>= next) := by
  intro env before result after run bounded targets
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  have firstResult := one env before value middle firstRun bounded targets
  exact two value env middle result after nextRun firstResult.1 firstResult.2

theorem EntryRun.of_targets {loop : Option LoopCtx} {action : B α}
    (_advance : AdvB action)
    (preserves : ∀ env before, EntryTargets before → LoopEntryTargets loop →
      EntryTargets (action env before).2) : EntryRun loop action := by
  intro env before result after run bounded targets
  have checked := preserves env before bounded targets
  rw [run] at checked
  exact ⟨checked, targets⟩

theorem EntryRun.withLoop {action : B α}
    (checked : EntryRun none action) (advance : AdvB action) (loop : Option LoopCtx) :
    EntryRun loop action := by
  apply EntryRun.of_targets advance
  intro env before bounded targets
  exact (checked env before _ _ rfl bounded trivial).1

theorem EntryRun.unchanged {loop : Option LoopCtx} {action : B α}
    (same : ∀ env state, (action env state).2 = state) : EntryRun loop action := by
  intro env before result after run bounded targets
  have equal := same env before
  rw [run] at equal
  change after = before at equal
  subst after
  exact ⟨bounded, targets⟩

theorem entry_pure (loop : Option LoopCtx) (value : α) :
    EntryRun loop (pure value) := EntryRun.unchanged (by intros; rfl)

theorem entry_read (loop : Option LoopCtx) :
    EntryRun loop (read : B LEnv) := EntryRun.unchanged (by intros; rfl)

theorem entry_get (loop : Option LoopCtx) :
    EntryRun loop (get : B LS) := EntryRun.unchanged (by intros; rfl)

theorem entry_emitDef (loop : Option LoopCtx) (op : Op) :
    EntryRun loop (emitDef op) := by
  apply EntryRun.of_targets (advB_emitDef op)
  intro env before bounded _
  exact bounded.emitDef op env

theorem entry_emitEffect (loop : Option LoopCtx) (effect : Effect) :
    EntryRun loop (emitEffect effect) := by
  apply EntryRun.of_targets (advB_emitEffect effect)
  intro env before bounded _
  exact bounded.emitEffect effect env

theorem entry_emitTerm (loop : Option LoopCtx) (term : Term)
    (references : ∀ _state : LS, LoopEntryTargets loop →
      ∀ target ∈ term.successors, target ≠ 0) :
    EntryRun loop (emitTerm term) := by
  apply EntryRun.of_targets (advB_emitTerm term)
  intro env before bounded targets
  exact bounded.emitTerm term (references before targets) env

theorem entry_recordValueRootRecipe (loop : Option LoopCtx) (value : ValueId) (sourceScope : ScopeId) :
    EntryRun loop (recordValueRootRecipe value sourceScope) := by
  apply EntryRun.of_targets (advB_recordValueRootRecipe value sourceScope)
  intro env before bounded _
  rw [recordValueRootRecipe_run]
  exact bounded.of_blocks rfl

theorem entry_newBlock (loop : Option LoopCtx) (types : List VTy) :
    EntryRun loop (newBlock types) := by
  intro env before result after run bounded targets
  rw [entry_newBlock_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨bounded.newBlock types env, targets⟩

theorem entry_setCur (loop : Option LoopCtx) (current : Option BlockId) :
    EntryRun loop (setCur current) := by
  intro env before result after run bounded targets
  rw [setCur_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨bounded.setCur current env, targets⟩

theorem entry_valTy (loop : Option LoopCtx) (value : ValueId) :
    EntryRun loop (valTy value) := by
  apply EntryRun.unchanged
  intro env state
  exact valTy_run value env state

theorem entry_intTyOf (loop : Option LoopCtx) (v : ValueId) : EntryRun loop (intTyOf v) := by
  unfold intTyOf
  refine EntryRun.bind (entry_valTy loop v) fun t => ?_
  cases t with
  | data t => cases t <;> exact entry_pure loop _
  | view _ _ => exact entry_pure loop _

theorem entry_freezeTo (loop : Option LoopCtx) (m : Mutability) (r : ValueId) : EntryRun loop (freezeTo m r) := by
  unfold freezeTo
  refine EntryRun.bind (entry_valTy loop r) fun t => ?_
  cases m <;> cases t <;> first
    | exact entry_pure loop _
    | (rename_i t; cases t <;> first | exact entry_pure loop _ | (rename_i m' _; cases m' <;> first | exact entry_pure loop _ | exact entry_emitDef loop _))

theorem entry_borrowTo (loop : Option LoopCtx) (mu : Mutability) (value : ValueId) : EntryRun loop (borrowTo mu value) := by
  intro env before result after run bounded targets
  rcases borrowTo_cases run with frozen | emitted
  · exact entry_freezeTo loop mu value env before result after frozen bounded targets
  · exact entry_emitDef loop _ env before result after emitted bounded targets

theorem entry_coerceTo (loop : Option LoopCtx) (target : Ty) (r : ValueId) (org : OriginId) : EntryRun loop (coerceTo target r org) := by
  unfold coerceTo
  refine EntryRun.bind (entry_valTy loop r) fun source => ?_
  split
  · exact entry_emitDef loop _
  · exact EntryRun.bind (entry_emitDef loop _) (fun _ => entry_emitDef loop _)
  · exact entry_pure loop _

theorem entry_coerceSlot (loop : Option LoopCtx) (slot : SlotId) (value : ValueId) (org : OriginId) :
    EntryRun loop (coerceSlot slot value org) := by
  unfold coerceSlot
  refine EntryRun.bind (entry_read loop) fun le => ?_
  cases le.slots[slot]? with
  | none => exact entry_pure loop _
  | some destination => exact entry_coerceTo loop _ _ _

theorem entry_coerceResult (loop : Option LoopCtx) (value : ValueId) (org : OriginId) :
    EntryRun loop (coerceResult value org) := by
  unfold coerceResult
  refine EntryRun.bind (entry_read loop) fun le => ?_
  cases le.results.head? with
  | none => exact entry_pure loop _
  | some destination => exact entry_coerceTo loop _ _ _

theorem entry_growOwner (loop : Option LoopCtx) (r : ValueId) : EntryRun loop (growOwner r) := by
  unfold growOwner
  refine EntryRun.bind (entry_valTy loop r) fun t => ?_
  cases t with
  | data t => cases t <;> first | exact entry_pure loop _ | (rename_i m' t'; cases t' <;> exact entry_pure loop _)
  | view _ _ => exact entry_pure loop _

theorem entry_leaveAll (loop : Option LoopCtx) : ∀ scs, EntryRun loop (leaveAll scs)
  | [] => entry_pure loop _
  | sc :: rest => by
    unfold leaveAll
    exact EntryRun.bind (entry_emitEffect loop _) fun _ => entry_leaveAll loop rest

theorem entry_leaveTo (loop : Option LoopCtx) (d : Nat) : EntryRun loop (leaveTo d) := by
  unfold leaveTo
  exact EntryRun.bind (entry_get loop) fun _ => entry_leaveAll loop _

theorem entry_initSlots (loop : Option LoopCtx) : ∀ ps, EntryRun loop (initSlots ps)
  | [] => entry_pure loop _
  | (s, v, o) :: rest => by
    unfold initSlots
    exact EntryRun.bind (entry_emitEffect loop _) fun _ => entry_initSlots loop rest

theorem entry_inScope {loop : Option LoopCtx} {action : B α} (scope : ScopeId)
    (body : EntryRun loop action) : EntryRun loop (inScope scope action) := by
  intro env before result after run bounded targets
  unfold inScope at run
  simp only [bind_eq] at run
  obtain ⟨ignored, entered, pushed, value, middle, bodyRun, ignoredNext, left, popped, finished⟩ := run
  rw [pushScope_run] at pushed
  obtain ⟨_, rfl⟩ := Prod.mk.inj pushed
  rw [pure_run] at finished
  obtain ⟨_, rfl⟩ := Prod.mk.inj finished
  rw [popScope_run] at popped
  obtain ⟨_, rfl⟩ := Prod.mk.inj popped
  have checked := body env _ _ _ bodyRun bounded targets
  exact checked

end Goose.Lower.Validation

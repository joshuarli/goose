import Goose.Lower.Validation.CfgTargetBounds
import Goose.Lower.Validate

namespace Goose.Lower

open Goose.Core Goose.GIR
open Goose.Lower.Validation

theorem TargetsBounded.instTargets {state : LS} (bounded : TargetsBounded state) :
    ∀ inst ∈ state.insts, ∀ target ∈ instTargetRefs inst, target < state.blocks.size := by
  intro inst member target referenced
  obtain ⟨body, bodyMember, instMember⟩ := List.mem_flatMap.mp member
  obtain ⟨index, located⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp bodyMember)
  apply bounded index body located target
  cases inst with
  | «def» value op => simp [instTargetRefs] at referenced
  | eff effect => simp [instTargetRefs] at referenced
  | term term =>
    apply List.mem_flatMap.mpr
    refine ⟨term, ?_, referenced⟩
    apply List.mem_filterMap.mpr
    exact ⟨.term term, instMember, rfl⟩

def LoopBuilderTargets (loop : Option LoopCtx) (state : LS) : Prop :=
  match loop with
  | none => True
  | some context => context.breakTo < state.blocks.size ∧
      match context.cont with
      | .jump header | .next header _ _ => header < state.blocks.size

theorem LoopBuilderTargets.mono {loop : Option LoopCtx} {before after : LS}
    (targets : LoopBuilderTargets loop before) (grows : before.blocks.size ≤ after.blocks.size) :
    LoopBuilderTargets loop after := by
  cases loop with
  | none => trivial
  | some context =>
    simp only [LoopBuilderTargets] at targets ⊢
    cases continuation : context.cont <;> simp only [continuation] at targets ⊢
    all_goals exact ⟨Nat.lt_of_lt_of_le targets.1 grows, Nat.lt_of_lt_of_le targets.2 grows⟩

def GeneratedTargetRun (loop : Option LoopCtx) (action : B α) : Prop :=
  ∀ env before result after, action env before = (result, after) →
    TargetsBounded before → LoopBuilderTargets loop before →
    TargetsBounded after ∧ LoopBuilderTargets loop after

theorem GeneratedTargetRun.bind {loop : Option LoopCtx} {first : B α} {next : α → B β}
    (one : GeneratedTargetRun loop first) (two : ∀ value, GeneratedTargetRun loop (next value)) :
    GeneratedTargetRun loop (first >>= next) := by
  intro env before result after run bounded targets
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  have firstResult := one env before value middle firstRun bounded targets
  exact two value env middle result after nextRun firstResult.1 firstResult.2

theorem GeneratedTargetRun.of_targets {loop : Option LoopCtx} {action : B α}
    (advance : AdvB action)
    (preserves : ∀ env before, TargetsBounded before → LoopBuilderTargets loop before →
      TargetsBounded (action env before).2) : GeneratedTargetRun loop action := by
  intro env before result after run bounded targets
  have checked := preserves env before bounded targets
  rw [run] at checked
  exact ⟨checked, targets.mono (advance env before result after run).ext.1⟩

theorem GeneratedTargetRun.withLoop {action : B α}
    (checked : GeneratedTargetRun none action) (advance : AdvB action) (loop : Option LoopCtx) :
    GeneratedTargetRun loop action := by
  apply GeneratedTargetRun.of_targets advance
  intro env before bounded targets
  exact (checked env before _ _ rfl bounded trivial).1

theorem GeneratedTargetRun.unchanged {loop : Option LoopCtx} {action : B α}
    (same : ∀ env state, (action env state).2 = state) : GeneratedTargetRun loop action := by
  intro env before result after run bounded targets
  have equal := same env before
  rw [run] at equal
  change after = before at equal
  subst after
  exact ⟨bounded, targets⟩

theorem generatedTargets_pure (loop : Option LoopCtx) (value : α) :
    GeneratedTargetRun loop (pure value) := GeneratedTargetRun.unchanged (by intros; rfl)

theorem generatedTargets_read (loop : Option LoopCtx) :
    GeneratedTargetRun loop (read : B LEnv) := GeneratedTargetRun.unchanged (by intros; rfl)

theorem generatedTargets_get (loop : Option LoopCtx) :
    GeneratedTargetRun loop (get : B LS) := GeneratedTargetRun.unchanged (by intros; rfl)

theorem generatedTargets_recordValueRootSource (loop : Option LoopCtx) (value : ValueId)
    (source : ValueRootSource) : GeneratedTargetRun loop (recordValueRootSource value source) := by
  intro env before result after run bounded targets
  rw [recordValueRootSource_run] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  exact ⟨bounded.of_blocks rfl, by cases loop <;> exact targets⟩

theorem generatedTargets_recordReadValueRootRecipe (loop : Option LoopCtx) (value : ValueId)
    (place : Place) : GeneratedTargetRun loop (recordReadValueRootRecipe value place) := by
  cases place with
  | var variableId =>
    unfold recordReadValueRootRecipe
    refine GeneratedTargetRun.bind (generatedTargets_read loop) fun env => ?_
    by_cases refSlice : (env.vars[variableId]?).any (fun localVar => localVar.ty.isRefSlice)
    · simp [refSlice]
      exact generatedTargets_recordValueRootSource loop value (.refSliceVar variableId)
    · simp [refSlice]
      exact generatedTargets_pure loop ()
  | global _ => simp [recordReadValueRootRecipe]; exact generatedTargets_pure loop ()
  | deref _ => simp [recordReadValueRootRecipe]; exact generatedTargets_pure loop ()
  | elem _ _ _ => simp [recordReadValueRootRecipe]; exact generatedTargets_pure loop ()
  | field _ _ => simp [recordReadValueRootRecipe]; exact generatedTargets_pure loop ()

theorem generatedTargets_recordValueRootRecipe (loop : Option LoopCtx) (value : ValueId) (sourceScope : ScopeId) :
    GeneratedTargetRun loop (recordValueRootRecipe value sourceScope) := by
  intro env before result after run bounded targets
  rw [recordValueRootRecipe_run] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  exact ⟨bounded.of_blocks rfl, by cases loop <;> exact targets⟩

theorem generatedTargets_emitDef (loop : Option LoopCtx) (op : Op) :
    GeneratedTargetRun loop (emitDef op) := by
  apply GeneratedTargetRun.of_targets (advB_emitDef op)
  intro env before bounded _
  exact bounded.emitDef op env

theorem generatedTargets_emitEffect (loop : Option LoopCtx) (effect : Effect) :
    GeneratedTargetRun loop (emitEffect effect) := by
  apply GeneratedTargetRun.of_targets (advB_emitEffect effect)
  intro env before bounded _
  exact bounded.emitEffect effect env

theorem generatedTargets_emitTerm (loop : Option LoopCtx) (term : Term)
    (references : ∀ state, LoopBuilderTargets loop state →
      ∀ target ∈ term.successors, target < state.blocks.size) :
    GeneratedTargetRun loop (emitTerm term) := by
  apply GeneratedTargetRun.of_targets (advB_emitTerm term)
  intro env before bounded targets
  exact bounded.emitTerm term (references before targets) env

theorem generatedTargets_newBlock (loop : Option LoopCtx) (types : List VTy) :
    GeneratedTargetRun loop (newBlock types) := by
  intro env before result after run bounded targets
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨bounded.newBlock types env, targets.mono (by simp)⟩

theorem generatedTargets_setCur (loop : Option LoopCtx) (current : Option BlockId) :
    GeneratedTargetRun loop (setCur current) := by
  intro env before result after run bounded targets
  rw [setCur_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨bounded.setCur current env, targets⟩

theorem generatedTargets_valTy (loop : Option LoopCtx) (value : ValueId) :
    GeneratedTargetRun loop (valTy value) := by
  apply GeneratedTargetRun.unchanged
  intro env state
  exact valTy_run value env state

theorem generatedTargets_intTyOf (loop : Option LoopCtx) (v : ValueId) : GeneratedTargetRun loop (intTyOf v) := by
  unfold intTyOf
  refine GeneratedTargetRun.bind (generatedTargets_valTy loop v) fun t => ?_
  cases t with
  | data t => cases t <;> exact generatedTargets_pure loop _
  | view _ _ => exact generatedTargets_pure loop _

theorem generatedTargets_freezeTo (loop : Option LoopCtx) (m : Mutability) (r : ValueId) : GeneratedTargetRun loop (freezeTo m r) := by
  unfold freezeTo
  refine GeneratedTargetRun.bind (generatedTargets_valTy loop r) fun t => ?_
  cases m <;> cases t <;> first
    | exact generatedTargets_pure loop _
    | (rename_i t; cases t <;> first | exact generatedTargets_pure loop _ | (rename_i m' _; cases m' <;> first | exact generatedTargets_pure loop _ | exact generatedTargets_emitDef loop _))

theorem generatedTargets_borrowTo (loop : Option LoopCtx) (m : Mutability) (r : ValueId) :
    GeneratedTargetRun loop (borrowTo m r) := by
  unfold borrowTo
  refine GeneratedTargetRun.bind (generatedTargets_read loop) fun le => ?_
  refine GeneratedTargetRun.bind (generatedTargets_valTy loop r) fun ty => ?_
  split <;> dsimp only <;> split <;> first
    | exact generatedTargets_emitDef loop _
    | exact generatedTargets_freezeTo loop _ r

theorem generatedTargets_coerceTo (loop : Option LoopCtx) (target : Ty) (r : ValueId) (org : OriginId) : GeneratedTargetRun loop (coerceTo target r org) := by
  unfold coerceTo
  refine GeneratedTargetRun.bind (generatedTargets_valTy loop r) fun source => ?_
  split
  · exact generatedTargets_emitDef loop _
  · exact GeneratedTargetRun.bind (generatedTargets_emitDef loop _) (fun _ => generatedTargets_emitDef loop _)
  · exact generatedTargets_pure loop _

theorem generatedTargets_coerceSlot (loop : Option LoopCtx) (slot : SlotId) (value : ValueId) (org : OriginId) :
    GeneratedTargetRun loop (coerceSlot slot value org) := by
  unfold coerceSlot
  refine GeneratedTargetRun.bind (generatedTargets_read loop) fun le => ?_
  cases le.slots[slot]? with
  | none => exact generatedTargets_pure loop _
  | some destination => exact generatedTargets_coerceTo loop _ _ _

theorem generatedTargets_coerceResult (loop : Option LoopCtx) (value : ValueId) (org : OriginId) :
    GeneratedTargetRun loop (coerceResult value org) := by
  unfold coerceResult
  refine GeneratedTargetRun.bind (generatedTargets_read loop) fun le => ?_
  cases le.results.head? with
  | none => exact generatedTargets_pure loop _
  | some destination => exact generatedTargets_coerceTo loop _ _ _

theorem generatedTargets_growOwner (loop : Option LoopCtx) (r : ValueId) : GeneratedTargetRun loop (growOwner r) := by
  unfold growOwner
  refine GeneratedTargetRun.bind (generatedTargets_valTy loop r) fun t => ?_
  cases t with
  | data t => cases t <;> first | exact generatedTargets_pure loop _ | (rename_i m' t'; cases t' <;> exact generatedTargets_pure loop _)
  | view _ _ => exact generatedTargets_pure loop _

theorem generatedTargets_leaveAll (loop : Option LoopCtx) : ∀ scs, GeneratedTargetRun loop (leaveAll scs)
  | [] => generatedTargets_pure loop _
  | sc :: rest => by
    unfold leaveAll
    exact GeneratedTargetRun.bind (generatedTargets_emitEffect loop _) fun _ => generatedTargets_leaveAll loop rest

theorem generatedTargets_leaveTo (loop : Option LoopCtx) (d : Nat) : GeneratedTargetRun loop (leaveTo d) := by
  unfold leaveTo
  exact GeneratedTargetRun.bind (generatedTargets_get loop) fun _ => generatedTargets_leaveAll loop _

theorem generatedTargets_initSlots (loop : Option LoopCtx) : ∀ ps, GeneratedTargetRun loop (initSlots ps)
  | [] => generatedTargets_pure loop _
  | (s, v, o) :: rest => by
    unfold initSlots
    exact GeneratedTargetRun.bind (generatedTargets_emitEffect loop _) fun _ => generatedTargets_initSlots loop rest

theorem generatedTargets_inScope {loop : Option LoopCtx} {action : B α} (scope : ScopeId)
    (body : GeneratedTargetRun loop action) : GeneratedTargetRun loop (inScope scope action) := by
  intro env before result after run bounded targets
  unfold inScope at run
  simp only [bind_eq] at run
  obtain ⟨unit, entered, pushed, value, middle, bodyRun, unit', left, popped, finished⟩ := run
  rw [pushScope_run] at pushed
  obtain ⟨_, rfl⟩ := Prod.mk.inj pushed
  rw [pure_run] at finished
  obtain ⟨_, rfl⟩ := Prod.mk.inj finished
  rw [popScope_run] at popped
  obtain ⟨_, rfl⟩ := Prod.mk.inj popped
  have checked := body env _ _ _ bodyRun bounded targets
  exact checked

end Goose.Lower

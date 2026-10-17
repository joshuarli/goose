import Goose.Lower.Validation.CfgUnreachableCode

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem UnreachableRun.unchanged {action : B α}
    (same : ∀ env state, (action env state).2 = state) : UnreachableRun action :=
  UnreachableRun.of_blocks (fun env state => congrArg LS.blocks (same env state))

theorem unreachable_pure (value : α) : UnreachableRun (pure value) := UnreachableRun.pure value

theorem unreachable_read : UnreachableRun (read : B LEnv) := UnreachableRun.unchanged (by intros; rfl)

theorem unreachable_get : UnreachableRun (get : B LS) := UnreachableRun.unchanged (by intros; rfl)

theorem unreachable_recordReadValueRootRecipe (value : ValueId) (place : Place) :
    UnreachableRun (recordReadValueRootRecipe value place) := by
  apply UnreachableRun.of_blocks
  intro env state
  cases place with
  | var variableId =>
    rw [recordReadValueRootRecipe_run]
    by_cases refSlice : (env.vars[variableId]?).any (fun localVar => localVar.ty.isRefSlice) = true <;>
      simp [refSlice, recordValueRootSource_run]
  | global _ => rw [recordReadValueRootRecipe_run]
  | deref _ => rw [recordReadValueRootRecipe_run]
  | elem _ _ _ => rw [recordReadValueRootRecipe_run]
  | field _ _ => rw [recordReadValueRootRecipe_run]

theorem unreachable_emitDef (op : Op) : UnreachableRun (emitDef op) := by
  intro env before result after run checked
  have emitted := checked.emitDef op env
  rw [run] at emitted
  exact emitted

theorem unreachable_emitEffect (effect : Effect) : UnreachableRun (emitEffect effect) := by
  intro env before result after run checked
  have emitted := checked.emitEffect effect env
  rw [run] at emitted
  exact emitted

theorem unreachable_emitTerm (term : Term) (ordinary : term ≠ .unreachable) :
    UnreachableRun (emitTerm term) := by
  intro env before result after run checked
  have emitted := checked.emitTerm term ordinary env
  rw [run] at emitted
  exact emitted

theorem unreachable_patchTerm (block : BlockId) (term : Term) (ordinary : term ≠ .unreachable) :
    UnreachableRun (patchTerm block term) := by
  intro env before result after run checked
  have emitted := checked.patchTerm block term ordinary env
  rw [run] at emitted
  exact emitted

theorem unreachable_newBlock (types : List VTy) : UnreachableRun (newBlock types) := by
  intro env before result after run checked
  have emitted := checked.newBlock types env
  rw [run] at emitted
  exact emitted

theorem unreachable_setCur (current : Option BlockId) : UnreachableRun (setCur current) := by
  intro env before result after run checked
  have emitted := checked.setCur current env
  rw [run] at emitted
  exact emitted

theorem unreachable_valTy (value : ValueId) :
    UnreachableRun (valTy value) := by
  apply UnreachableRun.unchanged
  intro env state
  exact valTy_run value env state

theorem unreachable_intTyOf (v : ValueId) : UnreachableRun (intTyOf v) := by
  unfold intTyOf
  refine UnreachableRun.bind (unreachable_valTy v) fun t => ?_
  cases t with
  | data t => cases t <;> exact unreachable_pure _
  | view _ _ => exact unreachable_pure _

theorem unreachable_freezeTo (m : Mutability) (r : ValueId) : UnreachableRun (freezeTo m r) := by
  unfold freezeTo
  refine UnreachableRun.bind (unreachable_valTy r) fun t => ?_
  cases m <;> cases t <;> first
    | exact unreachable_pure _
    | (rename_i t; cases t <;> first | exact unreachable_pure _ | (rename_i m' _; cases m' <;> first | exact unreachable_pure _ | exact unreachable_emitDef _))

theorem unreachable_borrowTo (mu : Mutability) (value : ValueId) : UnreachableRun (borrowTo mu value) := by
  intro env before result after run checked
  rcases borrowTo_cases run with frozen | emitted
  · exact unreachable_freezeTo mu value env before result after frozen checked
  · exact unreachable_emitDef _ env before result after emitted checked

theorem unreachable_coerceTo (target : Ty) (r : ValueId) (org : OriginId) : UnreachableRun (coerceTo target r org) := by
  unfold coerceTo
  refine UnreachableRun.bind (unreachable_valTy r) fun source => ?_
  split
  · exact unreachable_emitDef _
  · exact UnreachableRun.bind (unreachable_emitDef _) (fun _ => unreachable_emitDef _)
  · exact unreachable_pure _

theorem unreachable_coerceSlot (slot : SlotId) (value : ValueId) (org : OriginId) :
    UnreachableRun (coerceSlot slot value org) := by
  unfold coerceSlot
  refine UnreachableRun.bind (unreachable_read) fun le => ?_
  cases le.slots[slot]? with
  | none => exact unreachable_pure _
  | some destination => exact unreachable_coerceTo _ _ _

theorem unreachable_coerceResult (value : ValueId) (org : OriginId) :
    UnreachableRun (coerceResult value org) := by
  unfold coerceResult
  refine UnreachableRun.bind (unreachable_read) fun le => ?_
  cases le.results.head? with
  | none => exact unreachable_pure _
  | some destination => exact unreachable_coerceTo _ _ _

theorem unreachable_growOwner (r : ValueId) : UnreachableRun (growOwner r) := by
  unfold growOwner
  refine UnreachableRun.bind (unreachable_valTy r) fun t => ?_
  cases t with
  | data t => cases t <;> first | exact unreachable_pure _ | (rename_i m' t'; cases t' <;> exact unreachable_pure _)
  | view _ _ => exact unreachable_pure _

theorem unreachable_leaveAll : ∀ scs, UnreachableRun (leaveAll scs)
  | [] => unreachable_pure _
  | sc :: rest => by
    unfold leaveAll
    exact UnreachableRun.bind (unreachable_emitEffect _) fun _ => unreachable_leaveAll rest

theorem unreachable_leaveTo (d : Nat) : UnreachableRun (leaveTo d) := by
  unfold leaveTo
  exact UnreachableRun.bind (unreachable_get) fun _ => unreachable_leaveAll _

theorem unreachable_initSlots : ∀ ps, UnreachableRun (initSlots ps)
  | [] => unreachable_pure _
  | (s, v, o) :: rest => by
    unfold initSlots
    exact UnreachableRun.bind (unreachable_emitEffect _) fun _ => unreachable_initSlots rest

theorem unreachable_inScope {action : B α} (scope : ScopeId)
    (body : UnreachableRun action) : UnreachableRun (inScope scope action) := by
  unfold inScope
  refine UnreachableRun.bind (UnreachableRun.of_blocks ?_) fun _ => ?_
  · intros; rw [pushScope_run]
  refine UnreachableRun.bind body fun value => ?_
  refine UnreachableRun.bind (UnreachableRun.of_blocks ?_) fun _ => unreachable_pure value
  intros; rw [popScope_run]

end Goose.Lower.Validation

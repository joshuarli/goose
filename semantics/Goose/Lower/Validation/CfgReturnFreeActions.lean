import Goose.Lower.Validation.CfgReturnFreeBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ReturnFreeRun.unchanged {action : B α}
    (same : ∀ env state, (action env state).2 = state) : ReturnFreeRun action :=
  ReturnFreeRun.of_blocks (fun env state => congrArg LS.blocks (same env state))

theorem returnFree_recordValueRootRecipe (value : ValueId) (sourceScope : ScopeId) :
    ReturnFreeRun (recordValueRootRecipe value sourceScope) := by
  apply ReturnFreeRun.of_blocks
  intro env state
  rw [recordValueRootRecipe_run]

theorem returnFree_pure (value : α) : ReturnFreeRun (pure value) := ReturnFreeRun.pure value

theorem returnFree_read : ReturnFreeRun (read : B LEnv) := ReturnFreeRun.unchanged (by intros; rfl)

theorem returnFree_get : ReturnFreeRun (get : B LS) := ReturnFreeRun.unchanged (by intros; rfl)

theorem returnFree_recordReadValueRootRecipe (value : ValueId) (place : Place) :
    ReturnFreeRun (recordReadValueRootRecipe value place) := by
  apply ReturnFreeRun.of_blocks
  intro env before
  cases place <;> simp only [recordReadValueRootRecipe_run]
  split <;> simp [recordValueRootSource_run]

theorem returnFree_emitDef (op : Op) : ReturnFreeRun (emitDef op) := by
  intro env before result after run checked
  have emitted := checked.emitDef op env
  rw [run] at emitted
  exact emitted

theorem returnFree_emitEffect (effect : Effect) : ReturnFreeRun (emitEffect effect) := by
  intro env before result after run checked
  have emitted := checked.emitEffect effect env
  rw [run] at emitted
  exact emitted

theorem returnFree_emitTerm (term : Term) (ordinary : ReturnFreeTerm term) :
    ReturnFreeRun (emitTerm term) := by
  intro env before result after run checked
  have emitted := checked.emitTerm term ordinary env
  rw [run] at emitted
  exact emitted

theorem returnFree_patchTerm (block : BlockId) (term : Term) (ordinary : ReturnFreeTerm term) :
    ReturnFreeRun (patchTerm block term) := by
  intro env before result after run checked
  have emitted := checked.patchTerm block term ordinary env
  rw [run] at emitted
  exact emitted

theorem returnFree_newBlock (types : List VTy) : ReturnFreeRun (newBlock types) := by
  intro env before result after run checked
  have emitted := checked.newBlock types env
  rw [run] at emitted
  exact emitted

theorem returnFree_setCur (current : Option BlockId) : ReturnFreeRun (setCur current) := by
  intro env before result after run checked
  have emitted := checked.setCur current env
  rw [run] at emitted
  exact emitted

theorem returnFree_valTy (value : ValueId) :
    ReturnFreeRun (valTy value) := by
  apply ReturnFreeRun.unchanged
  intro env state
  exact valTy_run value env state

theorem returnFree_intTyOf (v : ValueId) : ReturnFreeRun (intTyOf v) := by
  unfold intTyOf
  refine ReturnFreeRun.bind (returnFree_valTy v) fun t => ?_
  cases t with
  | data t => cases t <;> exact returnFree_pure _
  | view _ _ => exact returnFree_pure _

theorem returnFree_freezeTo (m : Mutability) (r : ValueId) : ReturnFreeRun (freezeTo m r) := by
  unfold freezeTo
  refine ReturnFreeRun.bind (returnFree_valTy r) fun t => ?_
  cases m <;> cases t <;> first
    | exact returnFree_pure _
    | (rename_i t; cases t <;> first | exact returnFree_pure _ | (rename_i m' _; cases m' <;> first | exact returnFree_pure _ | exact returnFree_emitDef _))

theorem returnFree_borrowTo (mu : Mutability) (value : ValueId) : ReturnFreeRun (borrowTo mu value) := by
  intro env before result after run checked
  rcases borrowTo_cases run with frozen | emitted
  · exact returnFree_freezeTo mu value env before result after frozen checked
  · exact returnFree_emitDef _ env before result after emitted checked

theorem returnFree_coerceTo (target : Ty) (r : ValueId) (org : OriginId) : ReturnFreeRun (coerceTo target r org) := by
  unfold coerceTo
  refine ReturnFreeRun.bind (returnFree_valTy r) fun source => ?_
  split
  · exact returnFree_emitDef _
  · exact ReturnFreeRun.bind (returnFree_emitDef _) (fun _ => returnFree_emitDef _)
  · exact returnFree_pure _

theorem returnFree_coerceSlot (slot : SlotId) (value : ValueId) (org : OriginId) :
    ReturnFreeRun (coerceSlot slot value org) := by
  unfold coerceSlot
  refine ReturnFreeRun.bind (returnFree_read) fun le => ?_
  cases le.slots[slot]? with
  | none => exact returnFree_pure _
  | some destination => exact returnFree_coerceTo _ _ _

theorem returnFree_coerceResult (value : ValueId) (org : OriginId) :
    ReturnFreeRun (coerceResult value org) := by
  unfold coerceResult
  refine ReturnFreeRun.bind (returnFree_read) fun le => ?_
  cases le.results.head? with
  | none => exact returnFree_pure _
  | some destination => exact returnFree_coerceTo _ _ _

theorem returnFree_growOwner (r : ValueId) : ReturnFreeRun (growOwner r) := by
  unfold growOwner
  refine ReturnFreeRun.bind (returnFree_valTy r) fun t => ?_
  cases t with
  | data t => cases t <;> first | exact returnFree_pure _ | (rename_i m' t'; cases t' <;> exact returnFree_pure _)
  | view _ _ => exact returnFree_pure _

theorem returnFree_leaveAll : ∀ scs, ReturnFreeRun (leaveAll scs)
  | [] => returnFree_pure _
  | sc :: rest => by
    unfold leaveAll
    exact ReturnFreeRun.bind (returnFree_emitEffect _) fun _ => returnFree_leaveAll rest

theorem returnFree_leaveTo (d : Nat) : ReturnFreeRun (leaveTo d) := by
  unfold leaveTo
  exact ReturnFreeRun.bind (returnFree_get) fun _ => returnFree_leaveAll _

theorem returnFree_initSlots : ∀ ps, ReturnFreeRun (initSlots ps)
  | [] => returnFree_pure _
  | (s, v, o) :: rest => by
    unfold initSlots
    exact ReturnFreeRun.bind (returnFree_emitEffect _) fun _ => returnFree_initSlots rest

theorem returnFree_inScope {action : B α} (scope : ScopeId)
    (body : ReturnFreeRun action) : ReturnFreeRun (inScope scope action) := by
  unfold inScope
  refine ReturnFreeRun.bind (ReturnFreeRun.of_blocks ?_) fun _ => ?_
  · intros; rw [pushScope_run]
  refine ReturnFreeRun.bind body fun value => ?_
  refine ReturnFreeRun.bind (ReturnFreeRun.of_blocks ?_) fun _ => returnFree_pure value
  intros; rw [popScope_run]

theorem returnFree_call (callee : ContextId) (args : List ValueId) (origin : Option OriginId) :
    ReturnFreeRun (do
      let value ← emitDef (.call callee args origin)
      if (← read).mod.noReturn callee then emitTerm .unreachable
      pure value) := by
  refine ReturnFreeRun.bind (returnFree_emitDef _) fun value => ?_
  refine ReturnFreeRun.bind returnFree_read fun env => ?_
  cases env.mod.noReturn callee
  · exact returnFree_pure _
  · exact ReturnFreeRun.bind (returnFree_emitTerm _ (by intro values origin same; cases same)) fun _ => returnFree_pure _

end Goose.Lower.Validation

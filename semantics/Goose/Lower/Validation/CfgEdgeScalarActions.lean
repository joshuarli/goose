import Goose.Lower.Validation.CfgEdgeActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem edge_pure (value : α) : EdgeRun (pure value) := EdgeRun.pure value

theorem edge_intTyOf (v : ValueId) : EdgeRun (intTyOf v) := by
  unfold intTyOf
  refine EdgeRun.bind (edge_valTy v) fun t => ?_
  cases t with
  | data t => cases t <;> exact edge_pure _
  | view _ _ => exact edge_pure _

theorem edge_freezeTo (m : Mutability) (r : ValueId) : EdgeRun (freezeTo m r) := by
  unfold freezeTo
  refine EdgeRun.bind (edge_valTy r) fun t => ?_
  cases m <;> cases t <;> first
    | exact edge_pure _
    | (rename_i t; cases t <;> first | exact edge_pure _ | (rename_i m' _; cases m' <;> first | exact edge_pure _ | exact edge_emitDef _))

theorem edge_borrowTo (mu : Mutability) (value : ValueId) : EdgeRun (borrowTo mu value) := by
  intro env before result after run checked
  rcases borrowTo_cases run with frozen | emitted
  · exact edge_freezeTo mu value env before result after frozen checked
  · exact edge_emitDef _ env before result after emitted checked

theorem edge_coerceTo (target : Ty) (r : ValueId) (org : OriginId) : EdgeRun (coerceTo target r org) := by
  unfold coerceTo
  refine EdgeRun.bind (edge_valTy r) fun source => ?_
  split
  · exact edge_emitDef _
  · exact EdgeRun.bind (edge_emitDef _) (fun _ => edge_emitDef _)
  · exact edge_pure _

theorem edge_coerceSlot (slot : SlotId) (value : ValueId) (org : OriginId) :
    EdgeRun (coerceSlot slot value org) := by
  unfold coerceSlot
  refine EdgeRun.bind (edge_read) fun le => ?_
  cases le.slots[slot]? with
  | none => exact edge_pure _
  | some destination => exact edge_coerceTo _ _ _

theorem edge_coerceResult (value : ValueId) (org : OriginId) :
    EdgeRun (coerceResult value org) := by
  unfold coerceResult
  refine EdgeRun.bind (edge_read) fun le => ?_
  cases le.results.head? with
  | none => exact edge_pure _
  | some destination => exact edge_coerceTo _ _ _

theorem edge_growOwner (r : ValueId) : EdgeRun (growOwner r) := by
  unfold growOwner
  refine EdgeRun.bind (edge_valTy r) fun t => ?_
  cases t with
  | data t => cases t <;> first | exact edge_pure _ | (rename_i m' t'; cases t' <;> exact edge_pure _)
  | view _ _ => exact edge_pure _

theorem edge_leaveAll : ∀ scs, EdgeRun (leaveAll scs)
  | [] => edge_pure _
  | sc :: rest => by
    unfold leaveAll
    exact EdgeRun.bind (edge_emitEffect _) fun _ => edge_leaveAll rest

theorem edge_leaveTo (d : Nat) : EdgeRun (leaveTo d) := by
  unfold leaveTo
  exact EdgeRun.bind (edge_get) fun _ => edge_leaveAll _

theorem edge_initSlots : ∀ ps, EdgeRun (initSlots ps)
  | [] => edge_pure _
  | (s, v, o) :: rest => by
    unfold initSlots
    exact EdgeRun.bind (edge_emitEffect _) fun _ => edge_initSlots rest

theorem edge_inScope {action : B α} (scope : ScopeId)
    (body : EdgeRun action) : EdgeRun (inScope scope action) := by
  unfold inScope
  refine EdgeRun.bind (EdgeRun.of_tables ?_) fun _ => ?_
  · intros; rw [pushScope_run]; exact ⟨rfl, rfl⟩
  refine EdgeRun.bind body fun value => ?_
  refine EdgeRun.bind (EdgeRun.of_tables ?_) fun _ => EdgeRun.pure value
  intros; rw [popScope_run]; exact ⟨rfl, rfl⟩

end Goose.Lower.Validation

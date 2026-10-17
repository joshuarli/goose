import Goose.Lower.Validation.SummaryPreservationReturnFramesBuilder

namespace Goose.Lower.Validation.SummaryPreservation.ReturnFrames

open Goose.Core Goose.GIR

variable {avoid : List ValueId × Option OriginId}

theorem ReturnAbsentRun.unchanged {action : B α}
    (same : ∀ env state, (action env state).2 = state) : ReturnAbsentRun (avoid := avoid) action :=
  ReturnAbsentRun.of_blocks (fun env state => congrArg LS.blocks (same env state))

theorem returnAbsent_pure (value : α) : ReturnAbsentRun (avoid := avoid) (pure value) := ReturnAbsentRun.pure value

theorem returnAbsent_read : ReturnAbsentRun (avoid := avoid) (read : B LEnv) := ReturnAbsentRun.unchanged (by intros; rfl)

theorem returnAbsent_get : ReturnAbsentRun (avoid := avoid) (get : B LS) := ReturnAbsentRun.unchanged (by intros; rfl)

theorem returnAbsent_emitDef (op : Op) : ReturnAbsentRun (avoid := avoid) (emitDef op) := by
  intro env before result after run checked
  have emitted := checked.emitDef op env
  rw [run] at emitted
  exact emitted

theorem returnAbsent_emitEffect (effect : Effect) : ReturnAbsentRun (avoid := avoid) (emitEffect effect) := by
  intro env before result after run checked
  have emitted := checked.emitEffect effect env
  rw [run] at emitted
  exact emitted

theorem returnAbsent_emitTerm (term : Term) (ordinary : ReturnFreeTerm term) :
    ReturnAbsentRun (avoid := avoid) (emitTerm term) := by
  intro env before result after run checked
  have emitted := checked.emitTerm term ordinary env
  rw [run] at emitted
  exact emitted

theorem returnAbsent_patchTerm (block : BlockId) (term : Term) (ordinary : ReturnFreeTerm term) :
    ReturnAbsentRun (avoid := avoid) (patchTerm block term) := by
  intro env before result after run checked
  have emitted := checked.patchTerm block term ordinary env
  rw [run] at emitted
  exact emitted

theorem returnAbsent_newBlock (types : List VTy) : ReturnAbsentRun (avoid := avoid) (newBlock types) := by
  intro env before result after run checked
  have emitted := checked.newBlock types env
  rw [run] at emitted
  exact emitted

theorem returnAbsent_setCur (current : Option BlockId) : ReturnAbsentRun (avoid := avoid) (setCur current) := by
  intro env before result after run checked
  have emitted := checked.setCur current env
  rw [run] at emitted
  exact emitted

theorem returnAbsent_valTy (value : ValueId) :
    ReturnAbsentRun (avoid := avoid) (valTy value) := by
  apply ReturnAbsentRun.unchanged
  intro env state
  exact valTy_run value env state

theorem returnAbsent_intTyOf (v : ValueId) : ReturnAbsentRun (avoid := avoid) (intTyOf v) := by
  unfold intTyOf
  refine ReturnAbsentRun.bind (returnAbsent_valTy v) fun t => ?_
  cases t with
  | data t => cases t <;> exact returnAbsent_pure _
  | view _ _ => exact returnAbsent_pure _

theorem returnAbsent_freezeTo (m : Mutability) (r : ValueId) : ReturnAbsentRun (avoid := avoid) (freezeTo m r) := by
  unfold freezeTo
  refine ReturnAbsentRun.bind (returnAbsent_valTy r) fun t => ?_
  cases m <;> cases t <;> first
    | exact returnAbsent_pure _
    | (rename_i t; cases t <;> first | exact returnAbsent_pure _ | (rename_i m' _; cases m' <;> first | exact returnAbsent_pure _ | exact returnAbsent_emitDef _))

theorem returnAbsent_borrowTo (mu : Mutability) (value : ValueId) : ReturnAbsentRun (avoid := avoid) (borrowTo mu value) := by
  intro env before result after run checked
  rcases borrowTo_cases run with frozen | emitted
  · exact returnAbsent_freezeTo mu value env before result after frozen checked
  · exact returnAbsent_emitDef _ env before result after emitted checked

theorem returnAbsent_coerceTo (target : Ty) (r : ValueId) (org : OriginId) : ReturnAbsentRun (avoid := avoid) (coerceTo target r org) := by
  unfold coerceTo
  refine ReturnAbsentRun.bind (returnAbsent_valTy r) fun source => ?_
  split
  · exact returnAbsent_emitDef _
  · exact ReturnAbsentRun.bind (returnAbsent_emitDef _) (fun _ => returnAbsent_emitDef _)
  · exact returnAbsent_pure _

theorem returnAbsent_coerceSlot (slot : SlotId) (value : ValueId) (org : OriginId) :
    ReturnAbsentRun (avoid := avoid) (coerceSlot slot value org) := by
  unfold coerceSlot
  refine ReturnAbsentRun.bind (returnAbsent_read) fun le => ?_
  cases le.slots[slot]? with
  | none => exact returnAbsent_pure _
  | some destination => exact returnAbsent_coerceTo _ _ _

theorem returnAbsent_coerceResult (value : ValueId) (org : OriginId) :
    ReturnAbsentRun (avoid := avoid) (coerceResult value org) := by
  unfold coerceResult
  refine ReturnAbsentRun.bind (returnAbsent_read) fun le => ?_
  cases le.results.head? with
  | none => exact returnAbsent_pure _
  | some destination => exact returnAbsent_coerceTo _ _ _

theorem returnAbsent_growOwner (r : ValueId) : ReturnAbsentRun (avoid := avoid) (growOwner r) := by
  unfold growOwner
  refine ReturnAbsentRun.bind (returnAbsent_valTy r) fun t => ?_
  cases t with
  | data t => cases t <;> first | exact returnAbsent_pure _ | (rename_i m' t'; cases t' <;> exact returnAbsent_pure _)
  | view _ _ => exact returnAbsent_pure _

theorem returnAbsent_leaveAll : ∀ scs, ReturnAbsentRun (avoid := avoid) (leaveAll scs)
  | [] => returnAbsent_pure _
  | sc :: rest => by
    unfold leaveAll
    exact ReturnAbsentRun.bind (returnAbsent_emitEffect _) fun _ => returnAbsent_leaveAll rest

theorem returnAbsent_leaveTo (d : Nat) : ReturnAbsentRun (avoid := avoid) (leaveTo d) := by
  unfold leaveTo
  exact ReturnAbsentRun.bind (returnAbsent_get) fun _ => returnAbsent_leaveAll _

theorem returnAbsent_initSlots : ∀ ps, ReturnAbsentRun (avoid := avoid) (initSlots ps)
  | [] => returnAbsent_pure _
  | (s, v, o) :: rest => by
    unfold initSlots
    exact ReturnAbsentRun.bind (returnAbsent_emitEffect _) fun _ => returnAbsent_initSlots rest

theorem returnAbsent_inScope {action : B α} (scope : ScopeId)
    (body : ReturnAbsentRun (avoid := avoid) action) : ReturnAbsentRun (avoid := avoid) (inScope scope action) := by
  unfold inScope
  refine ReturnAbsentRun.bind (ReturnAbsentRun.of_blocks ?_) fun _ => ?_
  · intros; rw [pushScope_run]
  refine ReturnAbsentRun.bind body fun value => ?_
  refine ReturnAbsentRun.bind (ReturnAbsentRun.of_blocks ?_) fun _ => returnAbsent_pure value
  intros; rw [popScope_run]

theorem returnAbsent_call (callee : ContextId) (args : List ValueId) (origin : Option OriginId) :
    ReturnAbsentRun (avoid := avoid) (do
      let value ← emitDef (.call callee args origin)
      if (← read).mod.noReturn callee then emitTerm .unreachable
      pure value) := by
  refine ReturnAbsentRun.bind (returnAbsent_emitDef _) fun value => ?_
  refine ReturnAbsentRun.bind returnAbsent_read fun env => ?_
  cases env.mod.noReturn callee
  · exact returnAbsent_pure _
  · exact ReturnAbsentRun.bind (returnAbsent_emitTerm _ (by intro values origin same; cases same)) fun _ => returnAbsent_pure _

end Goose.Lower.Validation.SummaryPreservation.ReturnFrames

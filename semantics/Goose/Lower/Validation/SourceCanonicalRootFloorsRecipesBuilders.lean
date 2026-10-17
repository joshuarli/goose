import Goose.Lower.Validation.SourceCanonicalRootFloorsRecipesBasic

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR

theorem recipes_inScope (scope : ScopeId) {action : B α} (typed : RecipeRun action) :
    RecipeRun (inScope scope action) := by
  unfold inScope
  exact RecipeRun.bind (recipes_pushScope _) fun _ =>
    RecipeRun.bind typed fun _ => RecipeRun.bind recipes_popScope fun _ => RecipeRun.pure _

theorem recipes_whenLive (default : α) {action : BlockId → B α}
    (typed : ∀ block, RecipeRun (action block)) : RecipeRun (whenLive default action) := by
  unfold whenLive
  refine RecipeRun.bind recipes_curBlock fun current => ?_
  cases current
  · exact RecipeRun.pure _
  · exact typed _

theorem recipes_intTyOf (v : ValueId) : RecipeRun (intTyOf v) := by
  unfold intTyOf
  refine RecipeRun.bind (recipes_valTy v) fun t => ?_
  cases t with
  | data t => cases t <;> exact RecipeRun.pure _
  | view _ _ => exact RecipeRun.pure _

theorem recipes_freezeTo (m : Mutability) (r : ValueId) : RecipeRun (freezeTo m r) := by
  unfold freezeTo
  refine RecipeRun.bind (recipes_valTy r) fun t => ?_
  cases m <;> cases t <;> first
    | exact RecipeRun.pure _
    | (rename_i t; cases t <;> first | exact RecipeRun.pure _ | (rename_i m' _; cases m' <;> first | exact RecipeRun.pure _ | exact recipes_emitDef _))

theorem recipes_borrowTo (m : Mutability) (r : ValueId) : RecipeRun (borrowTo m r) := by
  unfold borrowTo
  refine RecipeRun.bind recipes_read fun le => RecipeRun.bind (recipes_valTy r) fun type => ?_
  split <;> dsimp only <;> first
    | exact recipes_freezeTo _ _
    | (split <;> first | exact recipes_emitDef _ | exact recipes_freezeTo _ _)

theorem recipes_coerceTo (target : Ty) (r : ValueId) (org : OriginId) : RecipeRun (coerceTo target r org) := by
  unfold coerceTo
  refine RecipeRun.bind (recipes_valTy r) fun source => ?_
  split
  · exact recipes_emitDef _
  · exact RecipeRun.bind (recipes_emitDef _) (fun _ => recipes_emitDef _)
  · exact RecipeRun.pure _

theorem recipes_coerceSlot (slot : SlotId) (value : ValueId) (org : OriginId) :
    RecipeRun (coerceSlot slot value org) := by
  unfold coerceSlot
  refine RecipeRun.bind recipes_read fun le => ?_
  cases le.slots[slot]? with
  | none => exact RecipeRun.pure _
  | some destination => exact recipes_coerceTo destination.ty value org

theorem recipes_coerceResult (value : ValueId) (org : OriginId) :
    RecipeRun (coerceResult value org) := by
  unfold coerceResult
  refine RecipeRun.bind recipes_read fun le => ?_
  cases le.results.head? with
  | none => exact RecipeRun.pure _
  | some destination => exact recipes_coerceTo destination value org

theorem recipes_growOwner (r : ValueId) : RecipeRun (growOwner r) := by
  unfold growOwner
  refine RecipeRun.bind (recipes_valTy r) fun t => ?_
  cases t with
  | data t => cases t <;> first | exact RecipeRun.pure _ | (rename_i m' t'; cases t' <;> exact RecipeRun.pure _)
  | view _ _ => exact RecipeRun.pure _

theorem recipes_leaveAll : ∀ scs, RecipeRun (leaveAll scs)
  | [] => RecipeRun.pure _
  | sc :: rest => by
    unfold leaveAll
    exact RecipeRun.bind (recipes_emitEffect _) fun _ => recipes_leaveAll rest

theorem recipes_leaveTo (d : Nat) : RecipeRun (leaveTo d) := by
  unfold leaveTo
  exact RecipeRun.bind recipes_get fun _ => recipes_leaveAll _

theorem recipes_initSlots : ∀ ps, RecipeRun (initSlots ps)
  | [] => RecipeRun.pure _
  | (s, v, o) :: rest => by
    unfold initSlots
    exact RecipeRun.bind (recipes_emitEffect _) fun _ => recipes_initSlots rest

theorem recipes_isLive : RecipeRun isLive := by
  unfold isLive
  exact RecipeRun.bind recipes_curBlock fun _ => RecipeRun.pure _

theorem recipes_eachElemValue (x : VarId) (byRef : Bool) (elem : ValueId) :
    RecipeRun (eachElemValue x byRef elem) := by
  unfold eachElemValue
  cases byRef
  · exact recipes_emitDef _
  · refine RecipeRun.bind recipes_read fun le => ?_
    cases le.vars[x]? with
    | none => exact RecipeRun.pure _
    | some lv =>
      dsimp only
      cases lv.ty with
      | ref m t => exact recipes_borrowTo m elem
      | _ => exact RecipeRun.pure _

theorem recipes_regrowOf (o : Option ValueId) : RecipeRun (regrowOf o) := by
  cases o with
  | none => exact RecipeRun.pure _
  | some r => exact recipes_growOwner r

theorem recipes_eachSampled (regrow : Bool) (vw : ValueId) : RecipeRun (eachSampled regrow vw) := by
  unfold eachSampled
  cases regrow
  · exact recipes_emitDef _
  · exact RecipeRun.pure _

theorem recipes_eachLen (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    RecipeRun (eachLen regrow owner sampled) := by
  unfold eachLen
  cases regrow
  · exact RecipeRun.pure _
  · exact recipes_emitDef _

theorem recipes_fork (condition : ValueId) : RecipeRun (fork condition) := by
  unfold fork
  exact RecipeRun.bind (recipes_newBlock _) fun ⟨thenBlock, _⟩ =>
    RecipeRun.bind (recipes_newBlock _) fun ⟨elseBlock, _⟩ =>
    RecipeRun.bind (recipes_emitTerm _) fun _ => RecipeRun.pure _

theorem recipes_patchBrs (target : BlockId) : ∀ incoming, RecipeRun (patchBrs target incoming)
  | [] => RecipeRun.pure _
  | (block, value) :: rest => by
    unfold patchBrs
    exact RecipeRun.bind (recipes_patchTerm _ _) fun _ => recipes_patchBrs target rest

theorem recipes_patchBrs0 (target : BlockId) : ∀ incoming, RecipeRun (patchBrs0 target incoming)
  | [] => RecipeRun.pure _
  | block :: rest => by
    unfold patchBrs0
    exact RecipeRun.bind (recipes_patchTerm _ _) fun _ => recipes_patchBrs0 target rest


end Goose.Lower.Validation.SourceCanonicalRootFloors

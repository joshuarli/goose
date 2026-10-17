import Goose.Lower.Validation.SourceValueRecipeTypesBasic

namespace Goose.Lower.Validation.SourceValueRecipeTypes

open Goose.Core Goose.GIR

theorem recipeTypes_inScope (scope : ScopeId) {action : B α} (typed : RecipeTypeRun action) :
    RecipeTypeRun (inScope scope action) := by
  unfold inScope
  exact RecipeTypeRun.bind (recipeTypes_pushScope _) fun _ =>
    RecipeTypeRun.bind typed fun _ => RecipeTypeRun.bind recipeTypes_popScope fun _ => RecipeTypeRun.pure _

theorem recipeTypes_whenLive (default : α) {action : BlockId → B α}
    (typed : ∀ block, RecipeTypeRun (action block)) : RecipeTypeRun (whenLive default action) := by
  unfold whenLive
  refine RecipeTypeRun.bind recipeTypes_curBlock fun current => ?_
  cases current
  · exact RecipeTypeRun.pure _
  · exact typed _

theorem recipeTypes_intTyOf (v : ValueId) : RecipeTypeRun (intTyOf v) := by
  unfold intTyOf
  refine RecipeTypeRun.bind (recipeTypes_valTy v) fun t => ?_
  cases t with
  | data t => cases t <;> exact RecipeTypeRun.pure _
  | view _ _ => exact RecipeTypeRun.pure _

theorem recipeTypes_freezeTo (m : Mutability) (r : ValueId) : RecipeTypeRun (freezeTo m r) := by
  unfold freezeTo
  refine RecipeTypeRun.bind (recipeTypes_valTy r) fun t => ?_
  cases m <;> cases t <;> first
    | exact RecipeTypeRun.pure _
    | (rename_i t; cases t <;> first | exact RecipeTypeRun.pure _ | (rename_i m' _; cases m' <;> first | exact RecipeTypeRun.pure _ | exact recipeTypes_emitDef _))

theorem recipeTypes_borrowTo (m : Mutability) (r : ValueId) : RecipeTypeRun (borrowTo m r) := by
  unfold borrowTo
  refine RecipeTypeRun.bind recipeTypes_read fun le => RecipeTypeRun.bind (recipeTypes_valTy r) fun type => ?_
  split <;> dsimp only <;> first
    | exact recipeTypes_freezeTo _ _
    | (split <;> first | exact recipeTypes_emitDef _ | exact recipeTypes_freezeTo _ _)

theorem recipeTypes_coerceTo (target : Ty) (r : ValueId) (org : OriginId) : RecipeTypeRun (coerceTo target r org) := by
  unfold coerceTo
  refine RecipeTypeRun.bind (recipeTypes_valTy r) fun source => ?_
  split
  · exact recipeTypes_emitDef _
  · exact RecipeTypeRun.bind (recipeTypes_emitDef _) (fun _ => recipeTypes_emitDef _)
  · exact RecipeTypeRun.pure _

theorem recipeTypes_coerceSlot (slot : SlotId) (value : ValueId) (org : OriginId) :
    RecipeTypeRun (coerceSlot slot value org) := by
  unfold coerceSlot
  refine RecipeTypeRun.bind recipeTypes_read fun le => ?_
  cases le.slots[slot]? with
  | none => exact RecipeTypeRun.pure _
  | some destination => exact recipeTypes_coerceTo destination.ty value org

theorem recipeTypes_coerceResult (value : ValueId) (org : OriginId) :
    RecipeTypeRun (coerceResult value org) := by
  unfold coerceResult
  refine RecipeTypeRun.bind recipeTypes_read fun le => ?_
  cases le.results.head? with
  | none => exact RecipeTypeRun.pure _
  | some destination => exact recipeTypes_coerceTo destination value org

theorem recipeTypes_growOwner (r : ValueId) : RecipeTypeRun (growOwner r) := by
  unfold growOwner
  refine RecipeTypeRun.bind (recipeTypes_valTy r) fun t => ?_
  cases t with
  | data t => cases t <;> first | exact RecipeTypeRun.pure _ | (rename_i m' t'; cases t' <;> exact RecipeTypeRun.pure _)
  | view _ _ => exact RecipeTypeRun.pure _

theorem recipeTypes_leaveAll : ∀ scs, RecipeTypeRun (leaveAll scs)
  | [] => RecipeTypeRun.pure _
  | sc :: rest => by
    unfold leaveAll
    exact RecipeTypeRun.bind (recipeTypes_emitEffect _) fun _ => recipeTypes_leaveAll rest

theorem recipeTypes_leaveTo (d : Nat) : RecipeTypeRun (leaveTo d) := by
  unfold leaveTo
  exact RecipeTypeRun.bind recipeTypes_get fun _ => recipeTypes_leaveAll _

theorem recipeTypes_initSlots : ∀ ps, RecipeTypeRun (initSlots ps)
  | [] => RecipeTypeRun.pure _
  | (s, v, o) :: rest => by
    unfold initSlots
    exact RecipeTypeRun.bind (recipeTypes_emitEffect _) fun _ => recipeTypes_initSlots rest

theorem recipeTypes_isLive : RecipeTypeRun isLive := by
  unfold isLive
  exact RecipeTypeRun.bind recipeTypes_curBlock fun _ => RecipeTypeRun.pure _

theorem recipeTypes_eachElemValue (x : VarId) (byRef : Bool) (elem : ValueId) :
    RecipeTypeRun (eachElemValue x byRef elem) := by
  unfold eachElemValue
  cases byRef
  · exact recipeTypes_emitDef _
  · refine RecipeTypeRun.bind recipeTypes_read fun le => ?_
    cases le.vars[x]? with
    | none => exact RecipeTypeRun.pure _
    | some lv =>
      dsimp only
      cases lv.ty with
      | ref m t => exact recipeTypes_borrowTo m elem
      | _ => exact RecipeTypeRun.pure _

theorem recipeTypes_regrowOf (o : Option ValueId) : RecipeTypeRun (regrowOf o) := by
  cases o with
  | none => exact RecipeTypeRun.pure _
  | some r => exact recipeTypes_growOwner r

theorem recipeTypes_eachSampled (regrow : Bool) (vw : ValueId) : RecipeTypeRun (eachSampled regrow vw) := by
  unfold eachSampled
  cases regrow
  · exact recipeTypes_emitDef _
  · exact RecipeTypeRun.pure _

theorem recipeTypes_eachLen (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    RecipeTypeRun (eachLen regrow owner sampled) := by
  unfold eachLen
  cases regrow
  · exact RecipeTypeRun.pure _
  · exact recipeTypes_emitDef _

theorem recipeTypes_fork (condition : ValueId) : RecipeTypeRun (fork condition) := by
  unfold fork
  exact RecipeTypeRun.bind (recipeTypes_newBlock _) fun ⟨thenBlock, _⟩ =>
    RecipeTypeRun.bind (recipeTypes_newBlock _) fun ⟨elseBlock, _⟩ =>
    RecipeTypeRun.bind (recipeTypes_emitTerm _) fun _ => RecipeTypeRun.pure _

theorem recipeTypes_patchBrs (target : BlockId) : ∀ incoming, RecipeTypeRun (patchBrs target incoming)
  | [] => RecipeTypeRun.pure _
  | (block, value) :: rest => by
    unfold patchBrs
    exact RecipeTypeRun.bind (recipeTypes_patchTerm _ _) fun _ => recipeTypes_patchBrs target rest

theorem recipeTypes_patchBrs0 (target : BlockId) : ∀ incoming, RecipeTypeRun (patchBrs0 target incoming)
  | [] => RecipeTypeRun.pure _
  | block :: rest => by
    unfold patchBrs0
    exact RecipeTypeRun.bind (recipeTypes_patchTerm _ _) fun _ => recipeTypes_patchBrs0 target rest


end Goose.Lower.Validation.SourceValueRecipeTypes

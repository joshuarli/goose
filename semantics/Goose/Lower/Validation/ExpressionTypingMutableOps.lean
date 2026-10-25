import Goose.Lower.Validation.ExpressionTypingSliceOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem tyPlace_field_mutable_binding {env : Core.TEnv} {owner : Place} {index : Nat}
    {info : PlaceInfo} {start placeFinish : Nat}
    (placeSource : Core.tyPlace env (.field owner index) start = .ok (info, placeFinish))
    (writable : info.referenceWritable env.mod.profile = true) :
    ∃ ownerInfo ownerFinish field fieldFinish,
      Core.tyPlace env owner start = .ok (ownerInfo, ownerFinish) ∧
      Core.structField env ownerInfo.ty index ownerFinish = .ok (field, fieldFinish) ∧
      info.ty = field.ty ∧ field.binding = .mutable := by
  have children := placeSource
  simp only [Core.tyPlace] at children
  obtain ⟨ownerInfo, ownerFinish, ownerSource, children⟩ := (st_bind_ok _ _ _ _).mp children
  obtain ⟨field, fieldFinish, fieldSource, children⟩ := (st_bind_ok _ _ _ _).mp children
  have pair := (st_pure_ok _ _ _).mp children
  have infoShape := congrArg Prod.fst pair
  dsimp only at infoShape
  have referent : info.ty = field.ty := congrArg PlaceInfo.ty infoShape
  obtain ⟨id, fields, ownerShape, flat, row, _⟩ := structField_ok _ _ _ _ _ _ fieldSource
  have fieldFlat := tyList_flat_get fields (by simpa [ownerShape, Ty.flat] using flat) index field.ty row
  have infoFlat : info.ty.flat = true := by rw [referent]; exact fieldFlat
  rw [flat_referenceWritable infoFlat] at writable
  have binding : field.binding = .mutable := by
    rw [infoShape] at writable
    simp only at writable
    have mutable := (Bool.and_eq_true_iff.mp writable).2
    cases binding : field.binding <;> simp_all
  exact ⟨ownerInfo, ownerFinish, field, fieldFinish, ownerSource, fieldSource, referent, binding⟩

theorem tyExpr_ref_mutable_field_binding {env : Core.TEnv} {owner : Place} {index : Nat}
    {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.ref .mutable (.field owner index)) start = .ok (ty, finish)) :
    ∃ ownerInfo ownerFinish field fieldFinish info placeFinish,
      Core.tyPlace env owner start = .ok (ownerInfo, ownerFinish) ∧
      Core.structField env ownerInfo.ty index ownerFinish = .ok (field, fieldFinish) ∧
      Core.tyPlace env (.field owner index) start = .ok (info, placeFinish) ∧
      ty = .ref .mutable info.ty ∧ info.ty = field.ty ∧ field.binding = .mutable := by
  obtain ⟨info, placeFinish, placeSource, shape, permission⟩ := tyExpr_ref_place source
  have writable : info.referenceWritable env.mod.profile = true := by
    cases bound : info.referenceWritable env.mod.profile <;> simp_all [Mutability.atLeast]
  obtain ⟨ownerInfo, ownerFinish, field, fieldFinish, ownerSource, fieldSource, referent, binding⟩ :=
    tyPlace_field_mutable_binding placeSource writable
  exact ⟨ownerInfo, ownerFinish, field, fieldFinish, info, placeFinish,
    ownerSource, fieldSource, placeSource, shape, referent, binding⟩

theorem lowerPlace_field_mutable_typed_of_owner {env : Core.TEnv} {owner : Place} {index : Nat}
    {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env (.field owner index) start = .ok (info, finish))
    (writable : info.referenceWritable env.mod.profile = true)
    {ownerInfo : PlaceInfo} {ownerFinish : Nat}
    (ownerSource : Core.tyPlace env owner start = .ok (ownerInfo, ownerFinish))
    {results : List Ty} {before mid : LS} {value : ValueId} {mu : Mutability} {block : BlockId}
    (ownerRun : lowerPlace owner (lowerEnv env.mod env.vars results) before = (value, mid))
    (ownerTyped : mid.vals[value]? = some (some (.data (.ref mu ownerInfo.ty))))
    (live : mid.cur = some block) :
    let (result, after) := lowerPlace (.field owner index) (lowerEnv env.mod env.vars results) before
    after.cur = mid.cur ∧ after.vals[result]? = some (some (.data (.ref .mutable info.ty))) := by
  obtain ⟨sourceOwner, sourceFinish, field, fieldFinish, child, fieldSource, referent, binding⟩ :=
    tyPlace_field_mutable_binding source writable
  rw [ownerSource] at child
  cases Except.ok.inj child
  obtain ⟨id, fields, descriptor, shape, descriptorRow, nominal, fieldRow⟩ := structField_descriptor fieldSource
  have operation : (Op.fieldAddr value index).resultTy (tyEnv (lowerEnv env.mod env.vars results) mid) =
      .ok (.data (.ref .mutable info.ty)) := by
    simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, lowerEnv,
      ownerTyped, shape, descriptorRow, nominal, fieldRow, referent, binding, Mutability.ofKind,
      pure, Except.pure, bind, Except.bind]
  simp only [lowerPlace, bind_run, ownerRun]
  have emitted := emitDef_recorded live operation
  exact ⟨emitted.2.1, emitted.2.2.1⟩

theorem lowerPlace_ref_mutable_field_typed_of_owner {env : Core.TEnv} {owner : Place} {index : Nat}
    {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.ref .mutable (.field owner index)) start = .ok (ty, finish))
    {ownerInfo : PlaceInfo} {ownerFinish : Nat}
    (ownerSource : Core.tyPlace env owner start = .ok (ownerInfo, ownerFinish))
    {results : List Ty} {before mid : LS} {value : ValueId} {mu : Mutability} {block : BlockId}
    (ownerRun : lowerPlace owner (lowerEnv env.mod env.vars results) before = (value, mid))
    (ownerTyped : mid.vals[value]? = some (some (.data (.ref mu ownerInfo.ty))))
    (live : mid.cur = some block) :
    let (result, after) := lowerPlace (.field owner index) (lowerEnv env.mod env.vars results) before
    after.cur = mid.cur ∧ after.vals[result]? = some (some (.data ty)) := by
  obtain ⟨info, placeFinish, placeSource, shape, permission⟩ := tyExpr_ref_place source
  have writable : info.referenceWritable env.mod.profile = true := by
    cases bound : info.referenceWritable env.mod.profile <;> simp_all [Mutability.atLeast]
  simpa only [shape] using lowerPlace_field_mutable_typed_of_owner placeSource writable ownerSource ownerRun ownerTyped live

#print axioms lowerPlace_ref_mutable_field_typed_of_owner

end Goose.Lower.Validation

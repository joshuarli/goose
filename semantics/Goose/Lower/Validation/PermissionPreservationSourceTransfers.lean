import Goose.Lower.Validation.PermissionPreservationSource
import Goose.Lower.Validation.ExpressionTypingSourceContents
import Goose.Lower.Validation.FieldTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem referenceWritable_same_contents {info : PlaceInfo} (profile : ArtifactProfile)
    (same : info.bindingWritable = info.contentsWritable) :
    info.referenceWritable profile = info.contentsWritable := by
  cases shape : info.ty <;> simp [PlaceInfo.referenceWritable, shape, same]

theorem source_place_reference_contents {env : Core.TEnv} {place : Place} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env place start = .ok (info, finish))
    (container : ContentsTarget info.ty) (reference : info.canReference place = true)
    (writable : info.referenceWritable env.mod.profile = true) : info.contentsWritable = true := by
  cases place with
  | var index =>
    unfold Core.tyPlace at source
    obtain ⟨descriptor, next, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    dsimp only at shape
    rw [shape]
  | global index =>
    unfold Core.tyPlace at source
    split at source
    · cases row : env.mod.globals[index]? with
      | none => simp [row, rej_ok] at source
      | some descriptor =>
        simp only [row] at source
        have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
        dsimp only at shape
        rw [shape]
    · exact (rej_ok _ _ _ _).mp source |>.elim
  | deref expression =>
    unfold Core.tyPlace at source
    obtain ⟨sourceTy, next, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    cases sourceTy <;> try exact (rej_ok _ _ _ _).mp source |>.elim
    case ref mu ty =>
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      dsimp only at shape
      have same : info.bindingWritable = info.contentsWritable := by rw [shape]
      rw [referenceWritable_same_contents env.mod.profile same] at writable
      exact writable
  | elem view index origin =>
    unfold Core.tyPlace at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨⟨element, mu⟩, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    dsimp only at shape
    have same : info.bindingWritable = info.contentsWritable := by rw [shape]
    rw [referenceWritable_same_contents env.mod.profile same] at writable
    exact writable
  | field owner index =>
    unfold Core.tyPlace at source
    obtain ⟨ownerInfo, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨field, _, fieldSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    dsimp only at shape
    have referent : info.ty = field.ty := congrArg PlaceInfo.ty shape
    obtain ⟨id, fields, ownerShape, flat, row, _⟩ := structField_ok _ _ _ _ _ _ fieldSource
    have fieldFlat := tyList_flat_get fields (by simpa [ownerShape, Ty.flat] using flat) index field.ty row
    have infoFlat : info.ty.flat = true := by rw [referent]; exact fieldFlat
    have binding : info.bindingWritable = true := by
      rw [flat_referenceWritable infoFlat] at writable
      exact writable
    cases shapeTy : info.ty <;>
      simp_all [ContentsTarget, PlaceInfo.canReference, Ty.flat]

theorem source_mutable_reference_permissions {env : Core.TEnv} {place : Place} {ty : Ty}
    {start finish : Nat} (source : Core.tyExpr env (.ref .mutable place) start = .ok (ty, finish)) :
    ∃ info next, Core.tyPlace env place start = .ok (info, next) ∧ ty = .ref .mutable info.ty ∧
      info.canReference place = true ∧ info.referenceWritable env.mod.profile = true := by
  unfold Core.tyExpr at source
  obtain ⟨info, next, placeSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, mid, fieldSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  have reference := (checkFieldReference_ok _ _ _ _).mp fieldSource
  have target : info.ty.refTarget = true := by
    by_cases target : info.ty.refTarget = true
    · exact target
    · simp [target, chk] at source
  simp only [target, ite_true] at source
  have writeBind : (requireWrite "a mutable reference" (info.referenceWritable env.mod.profile) >>=
      fun _ => pure (.ref .mutable info.ty)) mid = .ok (ty, finish) := by
    simpa [Functor.map, StateT.map] using source
  obtain ⟨_, _, writable, result⟩ := (st_bind_ok _ _ _ _).mp writeBind
  have permission := (requireWrite_ok _ _ _ _).mp writable
  have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp result)
  dsimp only at shape
  exact ⟨info, next, placeSource, shape, reference.1, permission.1⟩

theorem source_mutable_reference_contents {env : Core.TEnv} {place : Place} {referent : Ty}
    {start finish : Nat}
    (source : Core.tyExpr env (.ref .mutable place) start = .ok (.ref .mutable referent, finish))
    (container : ContentsTarget referent) :
    ∃ info next, Core.tyPlace env place start = .ok (info, next) ∧ info.ty = referent ∧
      info.contentsWritable = true := by
  obtain ⟨info, next, placeSource, shape, reference, writable⟩ := source_mutable_reference_permissions source
  have same : info.ty = referent := (Ty.ref.inj shape).2.symm
  refine ⟨info, next, placeSource, same, ?_⟩
  exact source_place_reference_contents placeSource (by rw [same]; exact container) reference writable

theorem source_argument_permissions {env : Core.TEnv} {callee : Core.Impl} {param : Param}
    {params : List Param} {mu : Mutability} {place : Place} {args : List Arg} {start finish : Nat}
    (source : Core.tyArgs env callee (param :: params) (.byRef mu place :: args) start = .ok ((), finish)) :
    ∃ localVar info childFinish restStart,
      callee.vars[param.var]? = some localVar ∧
      Core.tyPlace env place start = .ok (info, childFinish) ∧ info.canReference place = true ∧
      (mu = .mutable → info.referenceWritable env.mod.profile = true) ∧
      (Ty.ref mu info.ty).passableTo localVar.ty = true ∧
      Core.tyArgs env callee params args restStart = .ok ((), finish) := by
  simp only [Core.tyArgs, Core.argMode] at source
  by_cases mode : (Mode.byRef == param.mode) = true
  · simp only [mode, ite_true] at source
    cases row : callee.vars[param.var]? with
    | none => simp [row, chk] at source
    | some localVar =>
      simp only [row] at source
      obtain ⟨info, childFinish, childTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
      obtain ⟨_, fieldFinish, fieldSource, source⟩ := (st_bind_ok _ _ _ _).mp source
      have reference := (checkFieldReference_ok _ _ _ _).mp fieldSource
      by_cases target : (info.ty.refTarget ||
          (info.ty.isSlice && info.referenceWritable env.mod.profile && place.sliceArg)) = true
      · simp only [target, ite_true] at source
        cases mu with
        | readOnly =>
          by_cases permission : (Ty.ref .readOnly info.ty).passableTo localVar.ty = true
          · simp only [permission, ite_true] at source
            exact ⟨localVar, info, childFinish, fieldFinish, rfl, childTyped, reference.1,
              (by intro h; cases h), permission, source⟩
          · simp [permission, chk] at source
        | mutable =>
          have writeBind : (requireWrite "a mutable argument" (info.referenceWritable env.mod.profile) >>=
              fun _ => do
                unless (Ty.ref .mutable info.ty).passableTo localVar.ty do
                  rej .call s!"argument of a type or mutability the parameter {localVar.name} does not accept"
                Core.tyArgs env callee params args) fieldFinish = .ok ((), finish) := by
            simpa [Functor.map, StateT.map] using source
          obtain ⟨_, restStart, writable, source⟩ := (st_bind_ok _ _ _ _).mp writeBind
          have writePermission := (requireWrite_ok _ _ _ _).mp writable
          by_cases permission : (Ty.ref .mutable info.ty).passableTo localVar.ty = true
          · simp only [permission, ite_true] at source
            exact ⟨localVar, info, childFinish, restStart, rfl, childTyped, reference.1,
              fun _ => writePermission.1, permission, source⟩
          · simp [permission, chk] at source
      · simp [target, chk] at source
  · simp [mode, chk] at source

theorem source_mutable_argument_contents {env : Core.TEnv} {callee : Core.Impl} {param : Param}
    {params : List Param} {place : Place} {args : List Arg} {start finish : Nat}
    (source : Core.tyArgs env callee (param :: params) (.byRef .mutable place :: args) start = .ok ((), finish)) :
    ∃ localVar info childFinish restStart,
      callee.vars[param.var]? = some localVar ∧ Core.tyPlace env place start = .ok (info, childFinish) ∧
      (ContentsTarget info.ty → info.contentsWritable = true) ∧
      (Ty.ref .mutable info.ty).passableTo localVar.ty = true ∧
      Core.tyArgs env callee params args restStart = .ok ((), finish) := by
  obtain ⟨localVar, info, childFinish, restStart, row, placeSource, reference, writable, compatible, rest⟩ :=
    source_argument_permissions source
  exact ⟨localVar, info, childFinish, restStart, row, placeSource,
    fun container => source_place_reference_contents placeSource container reference (writable rfl), compatible, rest⟩

#print axioms source_place_reference_contents
#print axioms source_mutable_reference_contents
#print axioms source_mutable_argument_contents

end Goose.Lower.Validation

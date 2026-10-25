import Goose.Lower.Validation.SourceReadable

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound

def SourceReadablePlaceShape (env : TEnv) (place : Place) (type : Ty) : Prop :=
  (∃ index localVar, place = .var index ∧ env.vars[index]? = some localVar ∧ type = localVar.ty) ∨
  (∃ index localVar mu sliceMu element,
    place = .deref (.read (.var index)) ∧ env.vars[index]? = some localVar ∧
    localVar.ty = .ref mu (.slice sliceMu element) ∧ type = .slice sliceMu element ∧ element.flat = true)

private theorem global_nonref {env : TEnv} (checked : SourceReadableEnvironment env)
    {index : GlobalId} {globalVar : Global} (lookup : env.mod.globals[index]? = some globalVar) :
    globalVar.ty.isRefLike = false := by
  have accepted := checked.accepted
  unfold Core.validate at accepted
  obtain ⟨_, _, accepted⟩ := (ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, globals, _⟩ := (ex_bind_ok _ _ _).mp accepted
  have bound : index < env.mod.globals.size := (Array.getElem?_eq_some_iff.mp lookup).1
  have one := (forAll_ok _ _).mp globals index (List.mem_range.mpr bound)
  rw [lookup] at one
  cases reference : globalVar.ty.isRefLike with
  | false => rfl
  | true => simp [Core.checkGlobal, reference, chk] at one

private theorem slice_reference_place_shape {env : TEnv} {expression : Expr}
    {type : Ty} (special : Core.sliceRefTy env expression = some type)
    {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env (.deref expression) start = .ok (info, finish)) :
    SourceReadablePlaceShape env (.deref expression) info.ty := by
  cases expression with
  | read place =>
    cases place with
    | var index =>
      obtain ⟨localVar, row, localType, visible⟩ := sliceRefTy_variable_row special
      have reference := sliceRefTy_isRefSlice special
      simp only [Core.tyPlace, special] at source
      obtain ⟨actual, next, input, source⟩ := (st_bind_ok _ _ _ _).mp source
      have inputShape := congrArg Prod.fst ((st_pure_ok _ _ _).mp input)
      dsimp only at inputShape
      subst actual
      cases type with
      | ref mu target =>
        cases target with
        | slice sliceMu element =>
          have shape := congrArg (fun pair => pair.1.ty) ((st_pure_ok _ _ _).mp source)
          exact Or.inr ⟨index, localVar, mu, sliceMu, element, rfl, row, localType, shape, reference⟩
        | _ => simp [Ty.isRefSlice] at reference
      | _ => simp [Ty.isRefSlice] at reference
    | _ => simp [Core.sliceRefTy] at special
  | _ => simp [Core.sliceRefTy] at special

theorem source_readable_place_shape {env : TEnv} (checked : SourceReadableEnvironment env)
    {place : Place} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env place start = .ok (info, finish))
    (_readable : info.ty.readable = true) (reference : info.ty.isRefLike = true) :
    SourceReadablePlaceShape env place info.ty := by
  cases place with
  | var index =>
    simp only [Core.tyPlace] at source
    obtain ⟨localVar, next, lookup, source⟩ := (st_bind_ok _ _ _ _).mp source
    have row := (varOf_ok _ _ _ _).mp lookup |>.2.1
    have shape := congrArg (fun pair => pair.1.ty) ((st_pure_ok _ _ _).mp source)
    exact Or.inl ⟨index, localVar, rfl, row, shape⟩
  | global index =>
    by_cases available : index < env.globalLimit
    · cases row : env.mod.globals[index]? with
      | none => simp [Core.tyPlace, available, row, rej_ok] at source
      | some globalVar =>
        simp only [Core.tyPlace, available, row, ite_true] at source
        have shape := congrArg (fun pair => pair.1.ty) ((st_pure_ok _ _ _).mp source)
        have nonref := global_nonref checked row
        rw [shape, nonref] at reference
        cases reference
    · simp [Core.tyPlace, available, rej_ok] at source
  | deref expression =>
    cases special : Core.sliceRefTy env expression with
    | some type => exact slice_reference_place_shape special source
    | none =>
      obtain ⟨mu, next, childSource⟩ := tyPlace_deref_child special source
      have target := source_expression_refLike_readable expression checked childSource rfl
      have nonref := refTarget_not_refLike target
      rw [nonref] at reference
      cases reference
  | elem view index origin =>
    obtain ⟨viewStart, viewFinish, indexFinish, writable, integer, viewSource, indexSource⟩ :=
      tyPlace_elem_children source
    have nonref := refTarget_not_refLike (flat_refTarget (source_view_element_flat view checked viewSource))
    rw [nonref] at reference
    cases reference
  | field owner index =>
    simp only [Core.tyPlace] at source
    obtain ⟨ownerInfo, ownerFinish, ownerSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨field, fieldFinish, fieldSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    have shape := congrArg (fun pair => pair.1.ty) ((st_pure_ok _ _ _).mp source)
    obtain ⟨id, fields, ownerShape, flat, row, _⟩ := structField_ok _ _ _ _ _ _ fieldSource
    have fieldFlat := tyList_flat_get fields (by simpa [ownerShape, Ty.flat] using flat) index field.ty row
    have nonref := refTarget_not_refLike (flat_refTarget fieldFlat)
    rw [shape, nonref] at reference
    cases reference

theorem source_read_expression_shape {env : TEnv} (checked : SourceReadableEnvironment env)
    {place : Place} {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.read place) start = .ok (type, finish))
    (reference : type.isRefLike = true) : SourceReadablePlaceShape env place type := by
  simp only [Core.tyExpr] at source
  obtain ⟨info, next, placeSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  by_cases readable : info.ty.readable = true
  · simp only [readable, ite_true] at source
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    dsimp only at shape
    rw [shape] at reference ⊢
    exact source_readable_place_shape checked placeSource readable reference
  · simp [readable, rej_ok] at source

#print axioms source_readable_place_shape
#print axioms source_read_expression_shape

end Goose.Lower.Validation

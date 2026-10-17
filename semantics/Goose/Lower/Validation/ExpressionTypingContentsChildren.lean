import Goose.Lower.Validation.ExpressionTypingContentsSourceOps
import Goose.Lower.Validation.ExpressionTypingSourceContents

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem tyView_of_writable_place {env : Core.TEnv} {place : Place} {element : Ty} {start finish : Nat}
    (source : Core.tyView env (.of place) start = .ok ((element, true), finish)) :
    ∃ info next, Core.tyPlace env place start = .ok (info, next) ∧
      ContentsTarget info.ty ∧ info.contentsWritable = true := by
  simp only [Core.tyView] at source
  obtain ⟨info, next, child, source⟩ := (st_bind_ok _ _ _ _).mp source
  refine ⟨info, next, child, ?_⟩
  cases shape : info.ty <;> simp only [shape] at source
  all_goals try exact (rej_ok _ _ _ _).mp source |>.elim
  all_goals
    have pair := (st_pure_ok _ _ _).mp source
    have writable := congrArg (fun pair => pair.1.2) pair
    dsimp only at writable
    exact ⟨by trivial, writable.symm⟩

theorem tyPlace_deref_same_permissions {env : Core.TEnv} {expr : Expr} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env (.deref expr) start = .ok (info, finish)) :
    info.bindingWritable = info.contentsWritable := by
  simp only [Core.tyPlace] at source
  obtain ⟨target, next, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  cases target with
  | ref mu target =>
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    dsimp only at shape
    rw [shape]
  | _ => exact (rej_ok _ _ _ _).mp source |>.elim

theorem tyPlace_elem_same_permissions {env : Core.TEnv} {view : View} {index : Expr} {origin : OriginId}
    {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env (.elem view index origin) start = .ok (info, finish)) :
    info.bindingWritable = info.contentsWritable := by
  simp only [Core.tyPlace] at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
  dsimp only at shape
  rw [shape]

theorem sliceRefTy_isRefSlice {env : Core.TEnv} {expr : Expr} {target : Ty}
    (source : Core.sliceRefTy env expr = some target) : target.isRefSlice = true := by
  cases expr with
  | read place =>
    cases place with
    | var id =>
      by_cases visible : id ∈ env.visible
      · cases row : env.vars[id]? with
        | none => simp [Core.sliceRefTy, visible, row] at source
        | some localVar =>
          by_cases reference : localVar.ty.isRefSlice = true
          · simp only [Core.sliceRefTy, List.contains_iff_mem, visible, row, reference, ite_true, Option.some.injEq] at source
            rw [← source]
            exact reference
          · simp [Core.sliceRefTy, visible, row, reference] at source
      · simp [Core.sliceRefTy, visible] at source
    | _ => simp [Core.sliceRefTy] at source
  | _ => simp [Core.sliceRefTy] at source

theorem ContentsTarget.ref_not_refSlice {target : Ty} (container : ContentsTarget target) (mu : Mutability) :
    (Ty.ref mu target).isRefSlice = false := by
  cases target <;> simp_all [ContentsTarget, Ty.isRefSlice]

theorem tyPlace_deref_contents_child {env : Core.TEnv} {expr : Expr} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env (.deref expr) start = .ok (info, finish))
    (container : ContentsTarget info.ty) (contents : info.contentsWritable = true) :
    ∃ childFinish, Core.tyExpr env expr start = .ok (.ref .mutable info.ty, childFinish) := by
  have same := tyPlace_deref_same_permissions source
  have writable : info.referenceWritable env.mod.profile = true := by
    cases ty : info.ty <;> simp [PlaceInfo.referenceWritable, ty, same, contents]
  cases special : Core.sliceRefTy env expr with
  | none => exact tyPlace_deref_writable_child special source writable
  | some target =>
    have shape := tyPlace_deref_writable_special special source writable
    have reference := sliceRefTy_isRefSlice special
    rw [shape, container.ref_not_refSlice] at reference
    cases reference

theorem tyPlace_elem_contents_children {env : Core.TEnv} {view : View} {index : Expr} {origin : OriginId}
    {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env (.elem view index origin) start = .ok (info, finish))
    (contents : info.contentsWritable = true) :
    ∃ viewStart viewFinish indexFinish intTy,
      Core.tyView env view viewStart = .ok ((info.ty, true), viewFinish) ∧
      Core.tyExpr env index viewFinish = .ok (.int intTy, indexFinish) := by
  have same := tyPlace_elem_same_permissions source
  have writable : info.referenceWritable env.mod.profile = true := by
    cases ty : info.ty <;> simp [PlaceInfo.referenceWritable, ty, same, contents]
  exact tyPlace_elem_writable_children source writable

#print axioms tyPlace_deref_contents_child

end Goose.Lower.Validation

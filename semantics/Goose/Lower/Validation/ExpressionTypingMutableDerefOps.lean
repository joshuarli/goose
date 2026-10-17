import Goose.Lower.Validation.ExpressionTypingMutableOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem tyPlace_deref_writable_child {env : Core.TEnv} {expr : Expr} {info : PlaceInfo} {start finish : Nat}
    (ordinary : Core.sliceRefTy env expr = none)
    (source : Core.tyPlace env (.deref expr) start = .ok (info, finish))
    (writable : info.referenceWritable env.mod.profile = true) :
    ∃ childFinish, Core.tyExpr env expr start = .ok (.ref .mutable info.ty, childFinish) := by
  simp only [Core.tyPlace, ordinary] at source
  obtain ⟨referent, next, input, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨childTy, childFinish, childTyped, input⟩ := (st_bind_ok _ _ _ _).mp input
  by_cases referenceSlice : childTy.isRefSlice = true
  · simp [referenceSlice, chk] at input
  · simp only [referenceSlice] at input
    have inputPair := (st_pure_ok _ _ _).mp input
    have same : referent = childTy := congrArg Prod.fst inputPair
    subst referent
    cases childTy with
    | ref mu target =>
      have pair := (st_pure_ok _ _ _).mp source
      have shape := congrArg Prod.fst pair
      dsimp only at shape
      have targetShape : info.ty = target := congrArg PlaceInfo.ty shape
      rw [shape] at writable
      cases mu with
      | readOnly => cases target <;> simp [PlaceInfo.referenceWritable] at writable
      | mutable => exact ⟨childFinish, by simpa only [targetShape] using childTyped⟩
    | _ => exact (rej_ok _ _ _ _).mp source |>.elim

theorem tyPlace_deref_writable_special {env : Core.TEnv} {expr : Expr} {info : PlaceInfo}
    {target : Ty} {start finish : Nat}
    (special : Core.sliceRefTy env expr = some target)
    (source : Core.tyPlace env (.deref expr) start = .ok (info, finish))
    (writable : info.referenceWritable env.mod.profile = true) : target = .ref .mutable info.ty := by
  simp only [Core.tyPlace, special] at source
  obtain ⟨referent, next, input, source⟩ := (st_bind_ok _ _ _ _).mp source
  have pair := (st_pure_ok _ _ _).mp input
  have same : referent = target := congrArg Prod.fst pair
  subst referent
  cases target with
  | ref mu target =>
    have pair := (st_pure_ok _ _ _).mp source
    have shape := congrArg Prod.fst pair
    dsimp only at shape
    have referent : info.ty = target := congrArg PlaceInfo.ty shape
    rw [shape] at writable
    cases mu with
    | readOnly => cases target <;> simp [PlaceInfo.referenceWritable] at writable
    | mutable => rw [referent]
  | _ => exact (rej_ok _ _ _ _).mp source |>.elim

theorem lowerPlace_deref_writable_typed_of_child {env : Core.TEnv} {expr : Expr}
    {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env (.deref expr) start = .ok (info, finish))
    (writable : info.referenceWritable env.mod.profile = true)
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerPlace (.deref expr) (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (childTyped : ∀ childFinish,
      Core.tyExpr env expr start = .ok (.ref .mutable info.ty, childFinish) →
      after.vals[value]? = some (some (.data (.ref .mutable info.ty)))) :
    after.vals[value]? = some (some (.data (.ref .mutable info.ty))) := by
  cases special : Core.sliceRefTy env expr with
  | none =>
    obtain ⟨childFinish, childSource⟩ := tyPlace_deref_writable_child special source writable
    exact childTyped childFinish childSource
  | some target =>
    have shape := tyPlace_deref_writable_special special source writable
    subst target
    cases expr with
    | read place =>
      cases place with
      | var id =>
        have initial := (dead_lowerPlace (.deref (.read (.var id)))).live_before run live
        cases current : before.cur with
        | none => simp [current] at initial
        | some block =>
          have typed := lowerPlace_deref_refSlice_variable special source results before current
          rw [run] at typed
          exact typed.2
      | _ => simp [Core.sliceRefTy] at special
    | _ => simp [Core.sliceRefTy] at special

#print axioms lowerPlace_deref_writable_typed_of_child

end Goose.Lower.Validation

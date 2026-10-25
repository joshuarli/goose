import Goose.Lower.Validation.FieldTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerPlace_deref_typed_of_child {env : Core.TEnv} {expr : Expr} {info : PlaceInfo}
    {mu : Mutability} {target : Ty} {start childFinish finish : Nat}
    (ordinary : Core.sliceRefTy env expr = none)
    (childSource : Core.tyExpr env expr start = .ok (.ref mu target, childFinish))
    (source : Core.tyPlace env (.deref expr) start = .ok (info, finish))
    {vars : Array LocalVar} {results : List Ty} {before mid : LS} {value : ValueId}
    (childRun : lowerExpr expr (lowerEnv env.mod vars results) before = (value, mid))
    (childTyped : mid.vals[value]? = some (some (.data (.ref mu target)))) :
    let (result, after) := lowerPlace (.deref expr) (lowerEnv env.mod vars results) before
    after = mid ∧ after.vals[result]? = some (some (.data (.ref mu info.ty))) := by
  simp only [Core.tyPlace, ordinary] at source
  obtain ⟨referent, next, input, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨childTy, childEnd, child, input⟩ := (st_bind_ok _ _ _ _).mp input
  rw [childSource] at child
  cases Except.ok.inj child
  by_cases refSlice : (Ty.ref mu target).isRefSlice = true
  · simp [refSlice, chk] at input
  · simp only [refSlice] at input
    have pair := (st_pure_ok _ _ _).mp input
    have inputShape : referent = .ref mu target := congrArg Prod.fst pair
    subst referent
    have infoPair := (st_pure_ok _ _ _).mp source
    have referentType : info.ty = target := congrArg (fun pair => pair.1.ty) infoPair
    simpa only [lowerPlace, childRun] using
      (show mid = mid ∧ mid.vals[value]? = some (some (.data (.ref mu info.ty))) from
        ⟨rfl, by simpa only [referentType] using childTyped⟩)

theorem sliceRefTy_variable_row {env : Core.TEnv} {varId : VarId} {ty : Ty}
    (special : Core.sliceRefTy env (.read (.var varId)) = some ty) :
    ∃ localVar, env.vars[varId]? = some localVar ∧ localVar.ty = ty ∧ varId ∈ env.visible := by
  by_cases visible : varId ∈ env.visible
  · cases row : env.vars[varId]? with
    | none => simp [Core.sliceRefTy, visible, row] at special
    | some localVar =>
      by_cases reference : localVar.ty.isRefSlice = true
      · simp only [Core.sliceRefTy, List.contains_iff_mem, visible, row, reference, ite_true, Option.some.injEq] at special
        exact ⟨localVar, rfl, special, visible⟩
      · simp [Core.sliceRefTy, visible, row, reference] at special
  · simp [Core.sliceRefTy, visible] at special

theorem lowerPlace_deref_refSlice_variable {env : Core.TEnv} {varId : VarId} {info : PlaceInfo}
    {mu : Mutability} {target : Ty} {start finish : Nat}
    (special : Core.sliceRefTy env (.read (.var varId)) = some (.ref mu target))
    (source : Core.tyPlace env (.deref (.read (.var varId))) start = .ok (info, finish))
    (results : List Ty) (before : LS) {block : BlockId} (live : before.cur = some block) :
    let (value, after) := lowerPlace (.deref (.read (.var varId))) (lowerEnv env.mod env.vars results) before
    after.cur = before.cur ∧ after.vals[value]? = some (some (.data (.ref mu info.ty))) := by
  simp only [Core.tyPlace, special] at source
  obtain ⟨referent, next, input, source⟩ := (st_bind_ok _ _ _ _).mp source
  have inputPair := (st_pure_ok _ _ _).mp input
  have inputShape : referent = .ref mu target := congrArg Prod.fst inputPair
  subst referent
  have infoPair := (st_pure_ok _ _ _).mp source
  have referentType : info.ty = target := congrArg (fun pair => pair.1.ty) infoPair
  obtain ⟨localVar, row, localType, visible⟩ := sliceRefTy_variable_row special
  have variableSource : Core.tyPlace env (.var varId) start =
      .ok (⟨localVar.ty, localVar.kind == .mutable, true⟩, start) := by
    simp [Core.tyPlace, Core.varOf, visible, row, pure, StateT.pure, Except.pure, bind, StateT.bind, Except.bind]
  cases placeRun : lowerPlace (.var varId) (lowerEnv env.mod env.vars results) before with
  | mk value mid =>
    have place := lowerPlace_var_exact variableSource results before live
    rw [placeRun] at place
    dsimp only at place
    have loaded := lowerExpr_read_typed_of_place placeRun
      (by simpa only [referenceType] using place.2) (place.1.trans live)
    simpa only [lowerPlace, place.1, localType, referentType] using loaded

theorem tyPlace_deref_child {env : Core.TEnv} {expr : Expr} {info : PlaceInfo} {start finish : Nat}
    (ordinary : Core.sliceRefTy env expr = none)
    (source : Core.tyPlace env (.deref expr) start = .ok (info, finish)) :
    ∃ mu childFinish, Core.tyExpr env expr start = .ok (.ref mu info.ty, childFinish) := by
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
      have targetShape : info.ty = target := congrArg (fun pair => pair.1.ty) pair
      exact ⟨mu, childFinish, by simpa only [targetShape] using childTyped⟩
    | _ => exact (rej_ok _ _ _ _).mp source |>.elim

theorem lowerPlace_deref_read_variable_exact {env : Core.TEnv} {varId : VarId} {info : PlaceInfo}
    {start finish : Nat}
    (source : Core.tyPlace env (.deref (.read (.var varId))) start = .ok (info, finish))
    (results : List Ty) (before : LS) {block : BlockId} (live : before.cur = some block) :
    let (value, after) := lowerPlace (.deref (.read (.var varId))) (lowerEnv env.mod env.vars results) before
    ∃ mu, after.cur = before.cur ∧ after.vals[value]? = some (some (.data (.ref mu info.ty))) := by
  cases special : Core.sliceRefTy env (.read (.var varId)) with
  | none =>
    obtain ⟨mu, childFinish, childSource⟩ := tyPlace_deref_child special source
    refine ⟨mu, ?_⟩
    exact lowerExpr_read_var_exact childSource results before live
  | some ty =>
    have specialSource := source
    simp only [Core.tyPlace, special] at specialSource
    obtain ⟨referent, next, input, tail⟩ := (st_bind_ok _ _ _ _).mp specialSource
    have pair := (st_pure_ok _ _ _).mp input
    have same : referent = ty := congrArg Prod.fst pair
    subst referent
    cases ty with
    | ref mu target =>
      exact ⟨mu, lowerPlace_deref_refSlice_variable special source results before live⟩
    | _ => exact (rej_ok _ _ _ _).mp tail |>.elim

end Goose.Lower.Validation

import Goose.Lower.Validation.FunctionTables

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem tyExpr_call_nil_tables {env : Core.TEnv} {context : ContextId} {origin : OriginId}
    {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.call context [] origin) start = .ok (ty, finish)) :
    ∃ ctx callee resultStart, env.mod.contexts[context]? = some ctx ∧
      env.mod.impls[ctx.impl]? = some callee ∧ callee.params.size = 0 ∧
      Core.callResultTy callee resultStart = .ok (ty, finish) := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  cases contextRow : env.mod.contexts[context]? with
  | none => simp [contextRow, chk] at source
  | some ctx =>
    simp only [contextRow] at source
    cases calleeRow : env.mod.impls[ctx.impl]? with
    | none => simp [calleeRow, chk] at source
    | some callee =>
      simp only [calleeRow, List.length_nil] at source
      have noParams : callee.params.size = 0 := by
        by_cases noParams : callee.params.size = 0
        · exact noParams
        · simp [noParams, chk] at source
      simp only [noParams, ite_true] at source
      obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
      obtain ⟨_, resultStart, _, result⟩ := (st_bind_ok _ _ _ _).mp source
      exact ⟨ctx, callee, resultStart, rfl, calleeRow, noParams, result⟩

theorem call_nil_resultTy {le : LEnv} {state : LS} {function : FnId} {callee : Core.Impl}
    {ty : Ty} {start finish : Nat}
    (signature : le.sigs[function]? = some ([], callee.results.toList))
    (source : Core.callResultTy callee start = .ok (ty, finish)) (origin : OriginId) :
    (Op.call function [] (some origin)).resultTy (tyEnv le state) = .ok (.data ty) := by
  cases results : callee.results.toList with
  | nil =>
    simp only [Core.callResultTy, results] at source
    have shape : ty = .unit := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    simp [Op.resultTy, tyEnv, signature, results, shape, pure, Except.pure, bind, Except.bind]
  | cons result rest =>
    cases rest with
    | nil =>
      simp only [Core.callResultTy, results] at source
      have shape : ty = result := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      simp [Op.resultTy, tyEnv, signature, results, shape, pure, Except.pure, bind, Except.bind]
    | cons _ _ => simp [Core.callResultTy, results, chk] at source

private theorem call_tail_run (le : LEnv) (state : LS) (context : ContextId) (value : ValueId) :
    ((do
      if (← read).mod.noReturn context then emitTerm .unreachable
      pure value) : B ValueId) le state =
    if le.mod.noReturn context then
      (value, (emitTerm .unreachable le state).2) else (value, state) := by
  change (if le.mod.noReturn context then
    (fun e s => (value, (emitTerm .unreachable e s).2)) else
    (fun _ s => (value, s))) le state = _
  split <;> rfl

theorem lowerExpr_call_nil_typed {env : Core.TEnv} {context : ContextId} {origin : OriginId}
    {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.call context [] origin) start = .ok (ty, finish))
    (vars : Array LocalVar) (results : List Ty) (before : LS) :
    let (value, after) := lowerExpr (.call context [] origin) (lowerEnv env.mod vars results) before
    after.cur.isSome = true → after.vals[value]? = some (some (.data ty)) := by
  obtain ⟨ctx, callee, resultStart, contextRow, calleeRow, noParams, resultSource⟩ := tyExpr_call_nil_tables source
  have paramsNil : callee.params.toList = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa only [Array.length_toList] using noParams
  have signature : (lowerEnv env.mod vars results).sigs[ctx.impl]? = some ([], callee.results.toList) := by
    simp [lowerEnv, Array.getElem?_map, calleeRow, paramsNil]
  have contextRun : implOfContext context (lowerEnv env.mod vars results) before = (ctx.impl, before) := by
    change (((env.mod.contexts[context]?).map (·.impl)).getD 0, before) = (ctx.impl, before)
    rw [contextRow]
    rfl
  cases current : before.cur with
  | none =>
    intro live
    have stopped := dead_lowerExpr (.call context [] origin) (lowerEnv env.mod vars results) before
      _ _ rfl current
    simp [stopped] at live
  | some block =>
    have operation := call_nil_resultTy (state := before) signature resultSource origin
    cases emitted : emitDef (.call ctx.impl [] (some origin)) (lowerEnv env.mod vars results) before with
    | mk value middle =>
      have recorded := emitDef_recorded current operation
      rw [emitted] at recorded
      dsimp only at recorded
      have run : lowerExpr (.call context [] origin) (lowerEnv env.mod vars results) before =
          ((do
            if (← read).mod.noReturn context then emitTerm .unreachable
            pure value) : B ValueId) (lowerEnv env.mod vars results) middle := by
        simp only [lowerExpr]
        apply bind_eq.mpr
        refine ⟨[], before, rfl, ?_⟩
        apply bind_eq.mpr
        refine ⟨ctx.impl, before, contextRun, ?_⟩
        apply bind_eq.mpr
        exact ⟨value, middle, emitted, rfl⟩
      rw [run, call_tail_run]
      by_cases returns : (lowerEnv env.mod vars results).mod.noReturn context = true
      · have middleLive : middle.cur = some block := recorded.2.1.trans current
        simp only [returns, ite_true, emitTerm_run _ _ middleLive,
          Option.isSome_none, Bool.false_eq_true, false_implies]
      · simp only [returns]
        intro live
        exact recorded.2.2.1

theorem lowerPlace_deref_call_nil_typed {env : Core.TEnv} {context : ContextId}
    {origin : OriginId} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env (.deref (.call context [] origin)) start = .ok (info, finish))
    (vars : Array LocalVar) (results : List Ty) (before : LS) :
    let (value, after) := lowerPlace (.deref (.call context [] origin)) (lowerEnv env.mod vars results) before
    after.cur.isSome = true → ∃ mu, after.vals[value]? = some (some (.data (.ref mu info.ty))) := by
  have ordinary : Core.sliceRefTy env (.call context [] origin) = none := rfl
  obtain ⟨mu, childFinish, childSource⟩ := tyPlace_deref_child ordinary source
  intro live
  exact ⟨mu, lowerExpr_call_nil_typed childSource vars results before live⟩

end Goose.Lower.Validation

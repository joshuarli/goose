import Goose.Lower.Validation.ExpressionTypingBlocks
import Goose.Lower.ContextLowering

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

inductive PassableValues (state : LS) : List Ty → List ValueId → Prop where
  | nil : PassableValues state [] []
  | cons {param : Ty} {value : ValueId} {params : List Ty} {values : List ValueId}
      (head : ∃ actual, state.vals[value]? = some (some (.data actual)) ∧ actual.passableTo param = true)
      (tail : PassableValues state params values) : PassableValues state (param :: params) (value :: values)

theorem PassableValues.length_eq {state : LS} {params : List Ty} {values : List ValueId}
    (typed : PassableValues state params values) : params.length = values.length := by
  induction typed with
  | nil => rfl
  | cons _ _ inductionHypothesis => simpa only [List.length_cons] using congrArg Nat.succ inductionHypothesis

theorem PassableValues.retained {before after : LS} {params : List Ty} {values : List ValueId}
    (typed : PassableValues before params values) (retained : TypePrefix before after) :
    PassableValues after params values := by
  induction typed with
  | nil => exact .nil
  | @cons param value params values head tail inductionHypothesis =>
    obtain ⟨actual, recorded, permission⟩ := head
    exact .cons ⟨actual, retained value (.data actual) recorded, permission⟩ inductionHypothesis

private theorem passable_forIn {le : LEnv} {state : LS} {params : List Ty} {values : List ValueId}
    (typed : PassableValues state params values) :
    forIn (params.zip values) PUnit.unit (fun (param, value) _ => do
      unless (← (tyEnv le state).dataTy value).passableTo param do
        tyErr s!"argument %{value} is not accepted by its parameter"
      pure (ForInStep.yield PUnit.unit)) = .ok PUnit.unit := by
  induction typed with
  | nil => rfl
  | @cons param value params values head tail inductionHypothesis =>
    obtain ⟨actual, recorded, permission⟩ := head
    simp only [List.zip_cons_cons, List.forIn_cons]
    simpa [TyEnv.dataTy, TyEnv.valTy, tyEnv, recorded, permission,
      pure, Except.pure, bind, Except.bind] using inductionHypothesis

theorem call_resultTy_of_passable {le : LEnv} {state : LS} {function : FnId}
    {callee : Core.Impl} {params : List Ty} {values : List ValueId} {ty : Ty}
    {start finish : Nat}
    (signature : le.sigs[function]? = some (params, callee.results.toList))
    (typed : PassableValues state params values)
    (source : Core.callResultTy callee start = .ok (ty, finish)) (origin : OriginId) :
    (Op.call function values (some origin)).resultTy (tyEnv le state) = .ok (.data ty) := by
  have sameLength : params.length = values.length := PassableValues.length_eq typed
  have arguments := passable_forIn (le := le) typed
  simp only [Op.resultTy, tyEnv, signature]
  simp only [sameLength, ↓reduceIte]
  change (do
    for (param, value) in params.zip values do
      unless (← (tyEnv le state).dataTy value).passableTo param do
        tyErr s!"argument %{value} is not accepted by its parameter"
    match callee.results.toList with
    | [] => pure (VTy.data .unit)
    | [t] => pure (VTy.data t)
    | _ => tyErr s!"function {function} has several results") = .ok (.data ty)
  rw [arguments]
  cases results : callee.results.toList with
  | nil =>
    simp only [Core.callResultTy, results] at source
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    change ty = .unit at shape
    subst ty
    rfl
  | cons result rest =>
    cases rest with
    | nil =>
      simp only [Core.callResultTy, results] at source
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      change ty = result at shape
      subst ty
      rfl
    | cons _ _ => simp [Core.callResultTy, results, chk] at source

theorem tyExpr_call_tables {env : Core.TEnv} {context : ContextId} {args : List Arg}
    {origin : OriginId} {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.call context args origin) start = .ok (ty, finish)) :
    ∃ ctx callee argsStart argsFinish resultStart,
      env.mod.contexts[context]? = some ctx ∧ env.mod.impls[ctx.impl]? = some callee ∧
      callee.params.toList.length = args.length ∧
      Core.tyArgs env callee callee.params.toList args argsStart = .ok ((), argsFinish) ∧
      Core.callResultTy callee resultStart = .ok (ty, finish) := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, next, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  cases contextRow : env.mod.contexts[context]? with
  | none => simp [contextRow, chk] at source
  | some ctx =>
    simp only [contextRow] at source
    cases calleeRow : env.mod.impls[ctx.impl]? with
    | none => simp [calleeRow, chk] at source
    | some callee =>
      simp only [calleeRow] at source
      by_cases sameLength : callee.params.size = args.length
      · simp only [sameLength, ite_true] at source
        obtain ⟨argsResult, argsFinish, argsTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
        obtain ⟨_, resultStart, _, resultSource⟩ := (st_bind_ok _ _ _ _).mp source
        cases argsResult
        exact ⟨ctx, callee, next, argsFinish, resultStart, rfl, calleeRow,
          by simpa only [Array.length_toList] using sameLength, argsTyped, resultSource⟩
      · simp [sameLength, chk] at source

theorem tyArgs_byVal_head {env : Core.TEnv} {callee : Core.Impl} {param : Param}
    {params : List Param} {expr : Expr} {args : List Arg} {start finish : Nat}
    (source : Core.tyArgs env callee (param :: params) (.byVal expr :: args) start = .ok ((), finish)) :
    ∃ localVar argTy childStart childFinish restStart,
      callee.vars[param.var]? = some localVar ∧
      Core.tyExpr env expr childStart = .ok (argTy, childFinish) ∧
      argTy.passableTo localVar.ty = true ∧
      Core.tyArgs env callee params args restStart = .ok ((), finish) := by
  simp only [Core.tyArgs, Core.argMode] at source
  by_cases mode : (Mode.byValue == param.mode) = true
  · simp only [mode, ite_true] at source
    cases row : callee.vars[param.var]? with
    | none => simp [row, chk] at source
    | some localVar =>
      simp only [row] at source
      obtain ⟨argTy, childFinish, childTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
      by_cases permission : argTy.passableTo localVar.ty = true
      · simp only [permission, ite_true] at source
        exact ⟨localVar, argTy, start, childFinish, childFinish, rfl, childTyped, permission, source⟩
      · simp [permission, chk] at source
  · simp [mode, chk] at source

theorem call_result_tail_run (le : LEnv) (state : LS) (context : ContextId) (value : ValueId) :
    ((do
      if (← read).mod.noReturn context then emitTerm .unreachable
      pure value) : B ValueId) le state =
    if le.mod.noReturn context then
      (value, (emitTerm .unreachable le state).2) else (value, state) := by
  change (if le.mod.noReturn context then
    (fun e s => (value, (emitTerm .unreachable e s).2)) else
    (fun _ s => (value, s))) le state = _
  split <;> rfl

end Goose.Lower.Validation

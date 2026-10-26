import Goose.Lower.DemandGeneratedScalar
import Goose.Lower.DemandExpressionResult

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

def ScalarExpression.Inputs {expression : Expr} : ScalarExpression expression → Type
  | .literal .. | .boolean .. => Unit
  | .negate .. => Bool
  | .unary .. | .convert .. => IntTy × Int
  | .binary .. => IntTy × Int × Int
  | .compare .. => Sum (IntTy × Int × Int) (Bool × Bool)

def scalarOutcome (result : Except Stop Val) : M Val := fun state =>
  match result with
  | .ok value => .ok value state
  | .error stop => .stop stop state

def ScalarExpression.compute {expression : Expr} (form : ScalarExpression expression)
    (profile : NumProfile) (inputs : form.Inputs) : Except Stop Val :=
  match form with
  | .literal type number => .ok (.int type number)
  | .boolean value => .ok (.bool value)
  | .negate _ => .ok (.bool (!inputs))
  | .unary operation _ origin =>
      (evalUn profile operation inputs.1 inputs.2).mapError (fun kind => .abort (AbortKind.ofNum kind) origin)
        |>.map (Val.int inputs.1)
  | .convert kind target _ origin =>
      (evalConv profile kind inputs.1 target inputs.2).mapError (fun kind => .abort (AbortKind.ofNum kind) origin)
        |>.map (Val.int target)
  | .binary operation _ _ origin =>
      (evalBin profile operation inputs.1 inputs.2.1 inputs.2.2).mapError (fun kind => .abort (AbortKind.ofNum kind) origin)
        |>.map (Val.int inputs.1)
  | .compare operation _ _ =>
      match inputs with
      | .inl (_, left, right) => .ok (.bool (evalCmp operation left right))
      | .inr (left, right) => .ok (.bool (evalCmp operation (if left then 1 else 0) (if right then 1 else 0)))

def ScalarExpression.leftValue {operation : CmpOp} {left right : Expr} :
    (ScalarExpression.compare operation left right).Inputs → Val
  | .inl (type, left, _) => .int type left
  | .inr (left, _) => .bool left

def ScalarExpression.rightValue {operation : CmpOp} {left right : Expr} :
    (ScalarExpression.compare operation left right).Inputs → Val
  | .inl (type, _, right) => .int type right
  | .inr (_, right) => .bool right

def ScalarExpression.cells {expression : Expr} (form : ScalarExpression expression)
    (le : LEnv) (before : LS) (inputs : form.Inputs) : List (ValueId × RVal) :=
  match form with
  | .literal .. | .boolean .. => []
  | .negate child => [((lowerExpr child le before).1, .val (.bool inputs))]
  | .unary _ child _ | .convert _ _ child _ => [((lowerExpr child le before).1, .val (.int inputs.1 inputs.2))]
  | .binary _ left right _ =>
      [((lowerExpr left le before).1, .val (.int inputs.1 inputs.2.1)),
        ((lowerExpr right le (lowerExpr left le before).2).1, .val (.int inputs.1 inputs.2.2))]
  | .compare _ left right =>
      [((lowerExpr left le before).1, .val (ScalarExpression.leftValue inputs)),
        ((lowerExpr right le (lowerExpr left le before).2).1, .val (ScalarExpression.rightValue inputs))]

def ScalarExpression.PrefixEvaluated {expression : Expr} (form : ScalarExpression expression)
    (inputs : form.Inputs) (fuel : Nat) (cfg : Cfg) (env : Env) (state intermediate : St) : Prop :=
  match form with
  | .literal .. | .boolean .. => intermediate = state
  | .negate child => evalExpr fuel cfg env child state = .ok (.bool inputs) intermediate
  | .unary _ child _ | .convert _ _ child _ => evalExpr fuel cfg env child state = .ok (.int inputs.1 inputs.2) intermediate
  | .binary _ left right _ => ∃ afterLeft,
      evalExpr fuel cfg env left state = .ok (.int inputs.1 inputs.2.1) afterLeft ∧
      evalExpr fuel cfg env right afterLeft = .ok (.int inputs.1 inputs.2.2) intermediate
  | .compare _ left right => ∃ afterLeft,
      evalExpr fuel cfg env left state = .ok (ScalarExpression.leftValue inputs) afterLeft ∧
      evalExpr fuel cfg env right afterLeft = .ok (ScalarExpression.rightValue inputs) intermediate

theorem ScalarExpression.source_decompose {expression : Expr} (form : ScalarExpression expression)
    (inputs : form.Inputs) {fuel : Nat} {cfg : Cfg} {env : Env} {state intermediate : St}
    (evaluated : form.PrefixEvaluated inputs fuel cfg env state intermediate) :
    evalExpr (fuel + 1) cfg env expression state = scalarOutcome (form.compute cfg.profile inputs) intermediate := by
  cases form with
  | literal | boolean => subst intermediate; simp [evalExpr, compute, scalarOutcome, pure_apply]
  | negate => simp only [PrefixEvaluated] at evaluated; simp [evalExpr, bind_apply, evaluated, compute, scalarOutcome, Core.expectBool] <;> rfl
  | unary operation child origin =>
    simp only [PrefixEvaluated] at evaluated
    cases result : evalUn cfg.profile operation inputs.1 inputs.2 <;>
      simp [evalExpr, bind_apply, evaluated, compute, scalarOutcome, result, Core.expectInt, pure_apply, abortAt, M.stop, Except.map, Except.mapError]
  | convert kind target child origin =>
    simp only [PrefixEvaluated] at evaluated
    cases result : evalConv cfg.profile kind inputs.1 target inputs.2 <;>
      simp [evalExpr, bind_apply, evaluated, compute, scalarOutcome, result, Core.expectInt, Core.expectIntTy, pure_apply, abortAt, M.stop, Except.map, Except.mapError]
  | binary operation left right origin =>
    obtain ⟨afterLeft, leftDone, rightDone⟩ := evaluated
    cases result : evalBin cfg.profile operation inputs.1 inputs.2.1 inputs.2.2 <;>
      simp [evalExpr, bind_apply, leftDone, rightDone, compute, scalarOutcome, result, Core.expectInt,
        Core.expectSameTy, pure_apply, abortAt, M.stop, Except.map, Except.mapError]
  | compare operation left right =>
    obtain ⟨afterLeft, leftDone, rightDone⟩ := evaluated
    cases inputs with
    | inl integers =>
      rcases integers with ⟨type, first, second⟩
      simp [leftValue, rightValue] at leftDone rightDone
      simp [evalExpr, bind_apply, leftDone, rightDone, compute, scalarOutcome, expectComparable, expectSameTy, pure_apply]
    | inr booleans =>
      rcases booleans with ⟨first, second⟩
      simp [leftValue, rightValue] at leftDone rightDone
      simp [evalExpr, bind_apply, leftDone, rightDone, compute, scalarOutcome, expectComparable, pure_apply]

theorem ScalarExpression.instruction_decompose {expression : Expr} (form : ScalarExpression expression)
    (inputs : form.Inputs) {le : LEnv} {before : LS} {frame : GIR.Frame} {cx : FnCtx} {profile : NumProfile}
    (profileEq : cx.cfg.profile = profile)
    (has : ∀ cell ∈ form.cells le before inputs, frame.vals[cell.1]? = some cell.2)
    (fuel : Nat) (state : St) :
    execOp fuel cx frame (form.operation le before) state =
      match form.compute profile inputs with
      | .ok value => .ok (.val value) state
      | .error stop => .stop stop state := by
  cases form with
  | literal | boolean => simp [operation, execOp, execPure, compute, pure_apply]
  | negate child =>
    have cell := has ((lowerExpr child le before).1, .val (.bool inputs)) (by simp [cells])
    simp only [operation, execOp, execPure, getVal_of cell, pure_bind, Core.expectBool, compute]
    rfl
  | unary operation child origin =>
    have cell := has ((lowerExpr child le before).1, .val (.int inputs.1 inputs.2)) (by simp [cells])
    cases result : evalUn profile operation inputs.1 inputs.2 <;>
      simp [ScalarExpression.operation, execOp, execPure, getVal_of cell, pure_bind, Core.expectInt,
        profileEq, result, compute, Except.map, Except.mapError, pure_apply, abortAtOrg, abortAt, M.stop]
  | convert kind target child origin =>
    have cell := has ((lowerExpr child le before).1, .val (.int inputs.1 inputs.2)) (by simp [cells])
    cases result : evalConv profile kind inputs.1 target inputs.2 <;>
      simp [operation, execOp, execPure, getVal_of cell, pure_bind, Core.expectInt,
        profileEq, result, compute, Except.map, Except.mapError, pure_apply, abortAtOrg, abortAt, M.stop]
  | binary operation left right origin =>
    have first := has ((lowerExpr left le before).1, .val (.int inputs.1 inputs.2.1)) (by simp [cells])
    have second := has ((lowerExpr right le (lowerExpr left le before).2).1, .val (.int inputs.1 inputs.2.2)) (by simp [cells])
    cases result : evalBin profile operation inputs.1 inputs.2.1 inputs.2.2 <;>
      simp [ScalarExpression.operation, execOp, execPure, getVal_of first, getVal_of second, pure_bind,
        Core.expectInt, Core.expectSameTy, profileEq, result, compute, Except.map, Except.mapError,
        pure_apply, abortAtOrg, abortAt, M.stop]
  | compare operation left right =>
    have first := has ((lowerExpr left le before).1, .val (ScalarExpression.leftValue inputs)) (by simp [cells])
    have second := has ((lowerExpr right le (lowerExpr left le before).2).1, .val (ScalarExpression.rightValue inputs)) (by simp [cells])
    cases inputs with
    | inl integers =>
      rcases integers with ⟨type, firstNumber, secondNumber⟩
      simp only [ScalarExpression.leftValue] at first
      simp only [ScalarExpression.rightValue] at second
      simp only [ScalarExpression.operation]
      split <;> simp [execOp, execPure, getVal_of first, getVal_of second, pure_bind,
        expectComparable, expectSameTy, compute, pure_apply]
    | inr booleans =>
      rcases booleans with ⟨firstValue, secondValue⟩
      simp only [ScalarExpression.leftValue] at first
      simp only [ScalarExpression.rightValue] at second
      simp only [ScalarExpression.operation]
      split <;> simp [execOp, execPure, getVal_of first, getVal_of second, pure_bind,
        expectComparable, compute, pure_apply]

theorem ScalarExpression.compute_error_numeric {expression : Expr} (form : ScalarExpression expression)
    (inputs : form.Inputs) (profile : NumProfile) {stop : Stop}
    (failed : form.compute profile inputs = .error stop) :
    ∃ (kind : NumAbort) (origin : OriginId), stop = .abort (AbortKind.ofNum kind) origin := by
  cases form with
  | literal | boolean | negate => cases failed
  | unary operation child origin =>
    cases result : evalUn profile operation inputs.1 inputs.2 with
    | ok value => simp [compute, result, Except.map, Except.mapError] at failed
    | error kind =>
      simp only [compute, result, Except.mapError, Except.map, Except.error.injEq] at failed
      exact ⟨kind, origin, failed.symm⟩
  | convert kind target child origin =>
    cases result : evalConv profile kind inputs.1 target inputs.2 with
    | ok value => simp [compute, result, Except.map, Except.mapError] at failed
    | error abort =>
      simp only [compute, result, Except.mapError, Except.map, Except.error.injEq] at failed
      exact ⟨abort, origin, failed.symm⟩
  | binary operation left right origin =>
    cases result : evalBin profile operation inputs.1 inputs.2.1 inputs.2.2 with
    | ok value => simp [compute, result, Except.map, Except.mapError] at failed
    | error kind =>
      simp only [compute, result, Except.mapError, Except.map, Except.error.injEq] at failed
      exact ⟨kind, origin, failed.symm⟩
  | compare operation left right =>
    cases inputs <;> simp [compute] at failed

end Goose.Lower

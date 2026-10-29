import Goose.Lower.DemandCallNoReturn

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_actual_literal_call_success {cfg : Cfg} {env : Env} {state middle after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val}
    (argumentsDone : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    (fragment : WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    {expression : Expr} {literalValue : Val} {operation : Op}
    (literal : CallScalarLiteral expression literalValue operation) (hasValue : impl.body.value = some expression)
    {caller : Func} {before : LS} {results : List Ty} {initial frame : GIR.Frame} {start point : Pt}
    (wholePost : Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial
      (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2 frame point [])
    (read : mapList (getVal frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 middle = .ok values middle)
    (callerPoint : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {targetFuel : Nat} {value : Val}
    (executed : execOp targetFuel ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ frame
      (.call context (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 (some origin)) middle = .ok (.val value) after) :
    value = literalValue ∧ ∃ (afterCall : LS) (sourceFuel : Nat),
      evalExpr sourceFuel cfg env (.call context arguments origin) state = .ok value after ∧
      afterCall = (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 ∧
      RuntimeStep ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle (point.1, point.2 + 1)
        (frame.set (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.val value)) after ∧
      ExpressionDemandBoundary source map ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial afterCall
        (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 value after
        (point.1, point.2 + 1)
        (frame.set (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.val value)) := by
  obtain ⟨afterCall, calleeFuel, afterEq, calleePoint, calleeRun, post, step⟩ :=
    accepted_generated_call_execution_frontier source argumentsDone contextAt implAt depth wholePost read callerPoint extended executed
  obtain ⟨valueEq, bodyFuel, bodyDone⟩ :=
    accepted_generated_callee_literal_success source argumentsDone contextAt implAt fragment literal hasValue calleePoint calleeRun
  subst value
  have boundary := accepted_call_value_demand_return source argumentsDone contextAt implAt depth bodyDone admitted bounded realized post
  have evaluated := accepted_call_value_source_return source argumentsDone contextAt implAt depth bodyDone
  have noReturn := accepted_call_returning_not_noReturn evaluated
  have finalEq : afterCall = (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 := by
    rw [afterEq]
    simp [lowerExpr, bind_run, pure_run, lowerEnv, noReturn]
  exact ⟨rfl, afterCall, _, evaluated, finalEq, step, boundary⟩


theorem accepted_generated_actual_bool_call_success {cfg : Cfg} {env : Env} {state middle after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val}
    (argumentsDone : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    (fragment : WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    {boolean : Bool} (hasValue : impl.body.value = some (.bool boolean))
    {caller : Func} {before : LS} {results : List Ty} {initial frame : GIR.Frame} {start point : Pt}
    (wholePost : Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial
      (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2 frame point [])
    (read : mapList (getVal frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 middle = .ok values middle)
    (callerPoint : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {targetFuel : Nat} {value : Val}
    (executed : execOp targetFuel ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ frame
      (.call context (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 (some origin)) middle = .ok (.val value) after) :
    value = .bool boolean ∧ ∃ (afterCall : LS) (sourceFuel : Nat),
      evalExpr sourceFuel cfg env (.call context arguments origin) state = .ok value after ∧
      afterCall = (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 ∧
      RuntimeStep ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle (point.1, point.2 + 1)
        (frame.set (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.val value)) after ∧
      ExpressionDemandBoundary source map ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial afterCall
        (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 value after
        (point.1, point.2 + 1)
        (frame.set (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.val value)) := by
  exact accepted_generated_actual_literal_call_success source argumentsDone contextAt implAt depth fragment (.boolean boolean) hasValue wholePost read callerPoint extended admitted bounded realized executed

theorem accepted_generated_actual_unit_call_success_of_callee {cfg : Cfg} {env : Env} {state middle after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val}
    (argumentsDone : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    (reflect : ∀ {calleeFuel : Nat} {value : Val} {after : St},
      RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 0)
        (callFrame impl middle.nextAct (env.depth + 1) values) { middle with nextAct := middle.nextAct + 1 } →
      runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (0, 0)
        (callFrame impl middle.nextAct (env.depth + 1) values) calleeFuel { middle with nextAct := middle.nextAct + 1 } = .ok value after →
      value = .unit ∧ ∃ bodyFuel, execBlock bodyFuel cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
        ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
        { middle with nextAct := middle.nextAct + 1 } = .ok (.normal .unit) after)
    {caller : Func} {before : LS} {results : List Ty} {initial frame : GIR.Frame} {start point : Pt}
    (wholePost : Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial
      (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2 frame point [])
    (read : mapList (getVal frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 middle = .ok values middle)
    (callerPoint : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {targetFuel : Nat} {value : Val}
    (executed : execOp targetFuel ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ frame
      (.call context (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 (some origin)) middle = .ok (.val value) after) :
    value = .unit ∧ ∃ (afterCall : LS) (sourceFuel : Nat),
      evalExpr sourceFuel cfg env (.call context arguments origin) state = .ok value after ∧
      afterCall = (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 ∧
      RuntimeStep ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle (point.1, point.2 + 1)
        (frame.set (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.val value)) after ∧
      ExpressionDemandBoundary source map ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial afterCall
        (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 value after
        (point.1, point.2 + 1)
        (frame.set (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.val value)) := by
  obtain ⟨afterCall, calleeFuel, afterEq, calleePoint, calleeRun, post, step⟩ :=
    accepted_generated_call_execution_frontier source argumentsDone contextAt implAt depth wholePost read callerPoint extended executed
  obtain ⟨valueEq, bodyFuel, bodyDone⟩ :=
    reflect calleePoint calleeRun
  subst value
  have boundary := accepted_call_value_demand_return source argumentsDone contextAt implAt depth bodyDone admitted bounded realized post
  have evaluated := accepted_call_value_source_return source argumentsDone contextAt implAt depth bodyDone
  have noReturn := accepted_call_returning_not_noReturn evaluated
  have finalEq : afterCall = (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 := by
    rw [afterEq]
    simp [lowerExpr, bind_run, pure_run, lowerEnv, noReturn]
  exact ⟨rfl, afterCall, _, evaluated, finalEq, step, boundary⟩


theorem accepted_generated_actual_unit_call_success {cfg : Cfg} {env : Env} {state middle after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val}
    (argumentsDone : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    (fragment : WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    (noResults : impl.results.toList = []) (noValue : impl.body.value = none)
    {caller : Func} {before : LS} {results : List Ty} {initial frame : GIR.Frame} {start point : Pt}
    (wholePost : Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial
      (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2 frame point [])
    (read : mapList (getVal frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 middle = .ok values middle)
    (callerPoint : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {targetFuel : Nat} {value : Val}
    (executed : execOp targetFuel ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ frame
      (.call context (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 (some origin)) middle = .ok (.val value) after) :
    value = .unit ∧ ∃ (afterCall : LS) (sourceFuel : Nat),
      evalExpr sourceFuel cfg env (.call context arguments origin) state = .ok value after ∧
      afterCall = (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 ∧
      RuntimeStep ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle (point.1, point.2 + 1)
        (frame.set (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.val value)) after ∧
      ExpressionDemandBoundary source map ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial afterCall
        (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 value after
        (point.1, point.2 + 1)
        (frame.set (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.val value)) := by
  apply accepted_generated_actual_unit_call_success_of_callee source argumentsDone contextAt implAt depth ?_
    wholePost read callerPoint extended admitted bounded realized executed
  intro calleeFuel value after entry run
  exact accepted_generated_callee_unit_success source argumentsDone contextAt implAt fragment noResults noValue entry run

#print axioms accepted_generated_actual_unit_call_success_of_callee

#print axioms accepted_generated_actual_unit_call_success

#print axioms accepted_generated_actual_literal_call_success
#print axioms accepted_generated_actual_bool_call_success
end Goose.Lower

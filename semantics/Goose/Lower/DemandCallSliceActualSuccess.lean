import Goose.Lower.DemandCallSliceActualRun
import Goose.Lower.DemandCallActualSuccess

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_actual_slice_unit_call_success {cfg : Cfg} {env : Env} {state middle after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val}
    (argumentsDone : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    (fragment : SliceAssignmentStatements impl.body.stmts)
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
  obtain ⟨afterCall, calleeFuel, afterEq, calleePoint, calleeRun, post, step⟩ :=
    accepted_generated_call_execution_frontier source argumentsDone contextAt implAt depth wholePost read callerPoint extended executed
  obtain ⟨valueEq, bodyFuel, bodyDone⟩ :=
    accepted_generated_slice_callee_unit_success source argumentsDone contextAt implAt fragment noResults noValue calleePoint calleeRun
  subst value
  have boundary := accepted_call_value_demand_return source argumentsDone contextAt implAt depth bodyDone admitted bounded realized post
  have evaluated := accepted_call_value_source_return source argumentsDone contextAt implAt depth bodyDone
  have noReturn := accepted_call_returning_not_noReturn evaluated
  have finalEq : afterCall = (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 := by
    rw [afterEq]
    simp [lowerExpr, bind_run, pure_run, lowerEnv, noReturn]
  exact ⟨rfl, afterCall, _, evaluated, finalEq, step, boundary⟩


#print axioms accepted_generated_actual_slice_unit_call_success
end Goose.Lower

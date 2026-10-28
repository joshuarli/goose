import Goose.Lower.DemandCallMixedBodyLeave
import Goose.Lower.DemandCallArguments

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

theorem accepted_call_value_source_return {cfg : Cfg} {env : Env} {state middle after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel bodyFuel : Nat} {values : List Val} {value : Val}
    (argumentsDone : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    (bodyDone : execBlock bodyFuel cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
      { middle with nextAct := middle.nextAct + 1 } = .ok (.normal value) after) :
    evalExpr (max argumentFuel bodyFuel + 2) cfg env (.call context arguments origin) state = .ok value after := by
  let common := max argumentFuel bodyFuel
  have argumentsRaised : mapList (evalArg (common + 1) cfg env) arguments state = .ok values middle :=
    (MonoM.mapList (fun arg => (monoAll argumentFuel (common + 1) (by dsimp [common]; omega)).arg cfg env arg) arguments state).1 values middle argumentsDone
  have bodyRaised : execBlock common cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
      { middle with nextAct := middle.nextAct + 1 } = .ok (.normal value) after :=
    ((monoAll bodyFuel common (Nat.le_max_right argumentFuel bodyFuel)).block cfg
      ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩ _ impl.body _).1 _ _ bodyDone
  have arity := source.call_arguments_arity contextAt implAt argumentsDone
  change evalExpr (common + 2) cfg env (.call context arguments origin) state = .ok value after
  simp only [evalExpr, bind_apply, argumentsRaised, enterCall, Nat.not_le_of_lt depth, ↓reduceIte,
    lookupContext, lookupImpl, contextAt, implAt, pure_apply, arity, freshAct, bodyRaised, expectReturned]

theorem accepted_call_normal_source_return {cfg : Cfg} {env : Env} {state middle after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel bodyFuel : Nat} {values : List Val}
    (argumentsDone : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    (bodyDone : execBlock bodyFuel cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
      { middle with nextAct := middle.nextAct + 1 } = .ok (.normal .unit) after) :
    evalExpr (max argumentFuel bodyFuel + 2) cfg env (.call context arguments origin) state = .ok .unit after := by
  exact accepted_call_value_source_return source argumentsDone contextAt implAt depth bodyDone

theorem accepted_call_value_demand_return {cfg : Cfg} {env : Env} {state middle after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel bodyFuel : Nat} {values : List Val} {value : Val}
    (argumentsDone : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    (bodyDone : execBlock bodyFuel cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
      { middle with nextAct := middle.nextAct + 1 } = .ok (.normal value) after)
    {cx : FnCtx} {before built : LS} {initial frame : GIR.Frame} {start point : Pt} {id : ValueId}
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (post : Post cfg env cx before initial built frame point [(id, .val value)]) :
    ExpressionDemandBoundary source map cx before initial built id value after point frame := by
  have evaluated := accepted_call_value_source_return source argumentsDone contextAt implAt depth bodyDone
  exact ExpressionDemandBoundary.of_result (source.result _ value evaluated) admitted bounded realized post

theorem accepted_call_normal_demand_return {cfg : Cfg} {env : Env} {state middle after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel bodyFuel : Nat} {values : List Val}
    (argumentsDone : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    (bodyDone : execBlock bodyFuel cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
      { middle with nextAct := middle.nextAct + 1 } = .ok (.normal .unit) after)
    {cx : FnCtx} {before built : LS} {initial frame : GIR.Frame} {start point : Pt} {id : ValueId}
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (post : Post cfg env cx before initial built frame point [(id, .val .unit)]) :
    ExpressionDemandBoundary source map cx before initial built id .unit after point frame := by
  exact accepted_call_value_demand_return source argumentsDone contextAt implAt depth bodyDone admitted bounded realized post

#print axioms accepted_call_value_source_return
#print axioms accepted_call_value_demand_return
#print axioms accepted_call_normal_demand_return
#print axioms accepted_call_normal_source_return
end Goose.Lower

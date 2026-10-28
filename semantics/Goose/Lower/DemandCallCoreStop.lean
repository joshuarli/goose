import Goose.Lower.DemandCallCoreReturn

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

theorem accepted_call_source_stop {cfg : Cfg} {env : Env} {state middle after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel bodyFuel : Nat} {values : List Val} {stop : Stop}
    (argumentsDone : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth) (nonTimeout : stop ≠ .timeout)
    (bodyStopped : execBlock bodyFuel cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
      { middle with nextAct := middle.nextAct + 1 } = .stop stop after) :
    evalExpr (max argumentFuel bodyFuel + 2) cfg env (.call context arguments origin) state = .stop stop after := by
  let common := max argumentFuel bodyFuel
  have argumentsRaised : mapList (evalArg (common + 1) cfg env) arguments state = .ok values middle :=
    (MonoM.mapList (fun arg => (monoAll argumentFuel (common + 1) (by dsimp [common]; omega)).arg cfg env arg) arguments state).1 values middle argumentsDone
  have bodyRaised : execBlock common cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
      { middle with nextAct := middle.nextAct + 1 } = .stop stop after := by
    have promoted := ((monoAll bodyFuel common (Nat.le_max_right argumentFuel bodyFuel)).block cfg
      ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩ _ impl.body _).2 _ _ bodyStopped
    rcases promoted with timeout | preserved
    · cases stop <;> simp [isTimeout] at timeout nonTimeout
    · exact preserved
  have arity := source.call_arguments_arity contextAt implAt argumentsDone
  change evalExpr (common + 2) cfg env (.call context arguments origin) state = .stop stop after
  simp only [evalExpr, bind_apply, argumentsRaised, enterCall, Nat.not_le_of_lt depth, ↓reduceIte,
    lookupContext, lookupImpl, contextAt, implAt, pure_apply, arity, freshAct, bodyRaised]

#print axioms accepted_call_source_stop
end Goose.Lower

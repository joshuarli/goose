import Goose.Lower.DemandCallExecution

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_call_returning_not_noReturn {cfg : Cfg} {env : Env} {state after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId} {fuel : Nat} {value : Val}
    (evaluated : evalExpr fuel cfg env (.call context arguments origin) state = .ok value after) :
    cfg.mod.noReturn context = false := by
  cases status : cfg.mod.noReturn context with
  | false => rfl
  | true =>
    have never := never_call_expr cfg cfg.mod.noReturn (noReturn_sound cfg.mod cfg.profile)
      fuel env (.call context arguments origin) origin (by simpa using status)
    exact (never state value after evaluated).elim

#print axioms accepted_call_returning_not_noReturn
end Goose.Lower

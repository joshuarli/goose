import Goose.Lower.ReflectionInduction
import Goose.Lower.DemandRecursiveNestedCallModuleSuccess
import Goose.Lower.DemandRecursiveNestedCallModuleStop

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_validated_recursive_nested_call_module_success {cfg : Cfg} {fuel : Nat} {after : St}
    (accepted : Core.validate cfg.mod = .ok ())
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : ∀ (state middle : St), NestedCallLoopStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := [(impl.body.scope, middle.nextScope)], depth := 1 } impl.body.stmts)
    (noValue : impl.body.value = none)
    (run : GIR.runModule fuel ⟨cfg.profile, lower cfg.mod⟩ St.initial = .ok () after) :
    ∃ sourceFuel, Core.runModule sourceFuel cfg St.initial = .ok () after :=
  accepted_generated_recursive_nested_call_module_success accepted (fun residual _ id global globalAt => typedExpr_reflection residual cfg [global.ty] global.init)
    contextAt implAt fragment noValue run

#print axioms accepted_generated_validated_recursive_nested_call_module_success

theorem accepted_generated_validated_recursive_nested_call_module_nonTimeout_stop {cfg : Cfg} {fuel : Nat} {stop : Stop} {after : St}
    (accepted : Core.validate cfg.mod = .ok ())
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : ∀ (state middle : St), NestedCallLoopStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := [(impl.body.scope, middle.nextScope)], depth := 1 } impl.body.stmts)
    (noValue : impl.body.value = none)
    (nonTimeout : stop ≠ .timeout)
    (run : GIR.runModule fuel ⟨cfg.profile, lower cfg.mod⟩ St.initial = .stop stop after) :
    ∃ sourceFuel, Core.runModule sourceFuel cfg St.initial = .stop stop after :=
  accepted_generated_recursive_nested_call_module_nonTimeout_stop accepted (fun residual _ id global globalAt => typedExpr_reflection residual cfg [global.ty] global.init)
    contextAt implAt fragment noValue nonTimeout run

#print axioms accepted_generated_validated_recursive_nested_call_module_nonTimeout_stop

end Goose.Lower

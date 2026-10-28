import Goose.Lower.DemandWhileImmediateGlobals
import Goose.Lower.DemandRecursiveNestedCallModuleSuccess
import Goose.Lower.DemandRecursiveNestedCallModuleStop

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_immediate_recursive_nested_call_module_success {cfg : Cfg} {fuel : Nat} {after : St}
    (accepted : Core.validate cfg.mod = .ok ())
    (initializers : ImmediateGlobalInitializers cfg.mod)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : ∀ (state middle : St), NestedCallLoopStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := [(impl.body.scope, middle.nextScope)], depth := 1 } impl.body.stmts)
    (noValue : impl.body.value = none)
    (run : GIR.runModule fuel ⟨cfg.profile, lower cfg.mod⟩ St.initial = .ok () after) :
    ∃ sourceFuel, Core.runModule sourceFuel cfg St.initial = .ok () after :=
  accepted_generated_recursive_nested_call_module_success accepted (immediate_global_expression_reflection initializers) contextAt implAt fragment noValue run

#print axioms accepted_generated_immediate_recursive_nested_call_module_success

theorem accepted_generated_immediate_recursive_nested_call_module_nonTimeout_stop {cfg : Cfg} {fuel : Nat} {stop : Stop} {after : St}
    (accepted : Core.validate cfg.mod = .ok ())
    (initializers : ImmediateGlobalInitializers cfg.mod)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : ∀ (state middle : St), NestedCallLoopStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := [(impl.body.scope, middle.nextScope)], depth := 1 } impl.body.stmts)
    (noValue : impl.body.value = none)
    (nonTimeout : stop ≠ .timeout)
    (run : GIR.runModule fuel ⟨cfg.profile, lower cfg.mod⟩ St.initial = .stop stop after) :
    ∃ sourceFuel, Core.runModule sourceFuel cfg St.initial = .stop stop after :=
  accepted_generated_recursive_nested_call_module_nonTimeout_stop accepted (immediate_global_expression_reflection initializers) contextAt implAt fragment noValue nonTimeout run

#print axioms accepted_generated_immediate_recursive_nested_call_module_nonTimeout_stop

end Goose.Lower

import Goose.Lower.DemandWhileImmediateGlobals
import Goose.Lower.DemandWhileCallModuleSuccess
import Goose.Lower.DemandWhileCallModuleStop

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_immediate_scalar_call_loop_module_success {cfg : Cfg} {fuel : Nat} {after : St}
    (accepted : Core.validate cfg.mod = .ok ())
    (initializers : ImmediateGlobalInitializers cfg.mod)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (condition : Expr) (body : Core.Block) (loopOrigin : OriginId) (conditionForm : ControlPrefixExpression condition)
    (outerStatements : impl.body.stmts = [.while condition body loopOrigin]) (outerNoValue : impl.body.value = none)
    (fragment : ∀ (state middle : St), ReachableScalarCallStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := [(body.scope, middle.nextScope), (impl.body.scope, state.nextScope)], depth := 1 } body.stmts)
    (noValue : body.value = none)
    (run : GIR.runModule fuel ⟨cfg.profile, lower cfg.mod⟩ St.initial = .ok () after) :
    ∃ sourceFuel, Core.runModule sourceFuel cfg St.initial = .ok () after :=
  accepted_generated_scalar_call_loop_module_success accepted (immediate_global_expression_reflection initializers) contextAt implAt condition body loopOrigin
    conditionForm outerStatements outerNoValue fragment noValue run

#print axioms accepted_generated_immediate_scalar_call_loop_module_success

theorem accepted_generated_immediate_scalar_call_loop_module_nonTimeout_stop {cfg : Cfg} {fuel : Nat} {stop : Stop} {after : St}
    (accepted : Core.validate cfg.mod = .ok ())
    (initializers : ImmediateGlobalInitializers cfg.mod)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (condition : Expr) (body : Core.Block) (loopOrigin : OriginId) (conditionForm : ControlPrefixExpression condition)
    (outerStatements : impl.body.stmts = [.while condition body loopOrigin]) (outerNoValue : impl.body.value = none)
    (fragment : ∀ (state middle : St), ReachableScalarCallStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := [(body.scope, middle.nextScope), (impl.body.scope, state.nextScope)], depth := 1 } body.stmts)
    (noValue : body.value = none)
    (nonTimeout : stop ≠ .timeout)
    (run : GIR.runModule fuel ⟨cfg.profile, lower cfg.mod⟩ St.initial = .stop stop after) :
    ∃ sourceFuel, Core.runModule sourceFuel cfg St.initial = .stop stop after :=
  accepted_generated_scalar_call_loop_module_nonTimeout_stop accepted (immediate_global_expression_reflection initializers) contextAt implAt condition body loopOrigin
    conditionForm outerStatements outerNoValue fragment noValue nonTimeout run

#print axioms accepted_generated_immediate_scalar_call_loop_module_nonTimeout_stop

end Goose.Lower

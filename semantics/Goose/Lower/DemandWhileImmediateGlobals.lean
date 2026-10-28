import Goose.Lower.DemandWhileCompleteModuleSuccess
import Goose.Lower.DemandWhileCompleteModuleStop
import Goose.Lower.ReflectionTyped

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive ImmediateGlobalExpression : Expr → Prop
  | boolean (value : Bool) : ImmediateGlobalExpression (.bool value)
  | integer (type : IntTy) (value : Int) : ImmediateGlobalExpression (.lit type value)

def ImmediateGlobalInitializers (module : Core.Module) : Prop :=
  ∀ (id : GlobalId) (global : Core.Global), module.globals[id]? = some global → ImmediateGlobalExpression global.init

theorem ImmediateGlobalExpression.reflection {cfg : Cfg} {fuel : Nat} {results : List Ty} {expression : Expr}
    (form : ImmediateGlobalExpression expression) : TypedExprReflection fuel cfg results expression := by
  cases form with
  | boolean value => exact typedExprReflection_bool fuel cfg results value
  | integer type value => exact typedExprReflection_lit fuel cfg results type value

theorem immediate_global_expression_reflection {cfg : Cfg} {fuel : Nat}
    (initializers : ImmediateGlobalInitializers cfg.mod) :
    ∀ residual, residual + 1 = fuel → ∀ (id : GlobalId) (global : Core.Global),
      cfg.mod.globals[id]? = some global → TypedExprReflection residual cfg [global.ty] global.init := by
  intro residual equal id global globalAt
  exact (initializers id global globalAt).reflection

theorem accepted_generated_immediate_module_nonTimeout_stop {cfg : Cfg} {fuel : Nat} {stop : Stop} {after : St}
    (accepted : Core.validate cfg.mod = .ok ()) (initializers : ImmediateGlobalInitializers cfg.mod)
    (fragment : ∀ (state : St) (ctx : Context) (impl : Impl),
      cfg.mod.contexts[cfg.mod.entry]? = some ctx → cfg.mod.impls[ctx.impl]? = some impl →
      ∀ middle : St, WhileMixedStatements cfg
        { vars := impl.vars, act := state.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := 1 } impl.body.stmts)
    (noValue : ∀ (ctx : Context) (impl : Impl), cfg.mod.contexts[cfg.mod.entry]? = some ctx →
      cfg.mod.impls[ctx.impl]? = some impl → impl.body.value = none)
    (nonTimeout : stop ≠ .timeout)
    (run : GIR.runModule fuel ⟨cfg.profile, lower cfg.mod⟩ St.initial = .stop stop after) :
    ∃ sourceFuel, Core.runModule sourceFuel cfg St.initial = .stop stop after :=
  accepted_generated_module_nonTimeout_stop accepted (immediate_global_expression_reflection initializers)
    fragment noValue nonTimeout run

theorem accepted_generated_immediate_module_success {cfg : Cfg} {fuel : Nat} {after : St}
    (accepted : Core.validate cfg.mod = .ok ()) (initializers : ImmediateGlobalInitializers cfg.mod)
    (fragment : ∀ (state : St) (ctx : Context) (impl : Impl),
      cfg.mod.contexts[cfg.mod.entry]? = some ctx → cfg.mod.impls[ctx.impl]? = some impl →
      ∀ middle : St, WhileMixedStatements cfg
        { vars := impl.vars, act := state.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := 1 } impl.body.stmts)
    (noValue : ∀ (ctx : Context) (impl : Impl), cfg.mod.contexts[cfg.mod.entry]? = some ctx →
      cfg.mod.impls[ctx.impl]? = some impl → impl.body.value = none)
    (run : GIR.runModule fuel ⟨cfg.profile, lower cfg.mod⟩ St.initial = .ok () after) :
    ∃ sourceFuel, Core.runModule sourceFuel cfg St.initial = .ok () after :=
  accepted_generated_module_success accepted (immediate_global_expression_reflection initializers) fragment noValue run

#print axioms immediate_global_expression_reflection
#print axioms accepted_generated_immediate_module_nonTimeout_stop
#print axioms accepted_generated_immediate_module_success
end Goose.Lower

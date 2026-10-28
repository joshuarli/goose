import Goose.Lower.DemandRecursiveNestedCallImmediateGlobals

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive ClosedGlobalExpression : Expr → Prop
  | boolean (value : Bool) : ClosedGlobalExpression (.bool value)
  | integer (type : IntTy) (value : Int) : ClosedGlobalExpression (.lit type value)
  | not {expression : Expr} (child : ClosedGlobalExpression expression) : ClosedGlobalExpression (.not expression)
  | unary (operation : UnOp) (origin : OriginId) {expression : Expr} (child : ClosedGlobalExpression expression) :
      ClosedGlobalExpression (.un operation expression origin)
  | convert (kind : ConvKind) (target : Ty) (origin : OriginId) {expression : Expr} (child : ClosedGlobalExpression expression) :
      ClosedGlobalExpression (.conv kind target expression origin)
  | fill (target : Ty) {expression : Expr} (child : ClosedGlobalExpression expression) :
      ClosedGlobalExpression (.fill target expression)
  | binary (operation : BinOp) (origin : OriginId) {left right : Expr}
      (leftForm : ClosedGlobalExpression left) (rightForm : ClosedGlobalExpression right) :
      ClosedGlobalExpression (.bin operation left right origin)
  | compare (operation : CmpOp) {left right : Expr}
      (leftForm : ClosedGlobalExpression left) (rightForm : ClosedGlobalExpression right) :
      ClosedGlobalExpression (.cmp operation left right)

theorem ClosedGlobalExpression.reflection {cfg : Cfg} {results : List Ty} {expression : Expr}
    (form : ClosedGlobalExpression expression) : ∀ fuel : Nat, TypedExprReflection fuel cfg results expression := by
  induction form with
  | boolean value => intro fuel; exact typedExprReflection_bool fuel cfg results value
  | integer type value => intro fuel; exact typedExprReflection_lit fuel cfg results type value
  | not child ih => intro fuel; exact typedExprReflection_not (ih fuel)
  | unary operation origin child ih => intro fuel; exact typedExprReflection_un operation origin (ih fuel)
  | convert kind target origin child ih => intro fuel; exact typedExprReflection_conv kind target origin (ih fuel)
  | fill target child ih => intro fuel; exact typedExprReflection_fill target (ih fuel)
  | binary operation origin leftForm rightForm leftIH rightIH =>
    intro fuel
    exact typedExprReflection_bin operation origin (leftIH fuel) (fun residual _ => rightIH residual)
  | compare operation leftForm rightForm leftIH rightIH =>
    intro fuel
    exact typedExprReflection_cmp operation (leftIH fuel) (fun residual _ => rightIH residual)

def ClosedGlobalInitializers (module : Core.Module) : Prop :=
  ∀ (id : GlobalId) (global : Core.Global), module.globals[id]? = some global → ClosedGlobalExpression global.init

theorem closed_global_expression_reflection {cfg : Cfg} {fuel : Nat}
    (initializers : ClosedGlobalInitializers cfg.mod) :
    ∀ residual, residual + 1 = fuel → ∀ (id : GlobalId) (global : Core.Global),
      cfg.mod.globals[id]? = some global → TypedExprReflection residual cfg [global.ty] global.init := by
  intro residual equal id global globalAt
  exact (initializers id global globalAt).reflection residual

theorem accepted_generated_closed_recursive_nested_call_module_success {cfg : Cfg} {fuel : Nat} {after : St}
    (accepted : Core.validate cfg.mod = .ok ())
    (initializers : ClosedGlobalInitializers cfg.mod)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : ∀ (state middle : St), NestedCallLoopStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := [(impl.body.scope, middle.nextScope)], depth := 1 } impl.body.stmts)
    (noValue : impl.body.value = none)
    (run : GIR.runModule fuel ⟨cfg.profile, lower cfg.mod⟩ St.initial = .ok () after) :
    ∃ sourceFuel, Core.runModule sourceFuel cfg St.initial = .ok () after :=
  accepted_generated_recursive_nested_call_module_success accepted (closed_global_expression_reflection initializers) contextAt implAt fragment noValue run

#print axioms accepted_generated_closed_recursive_nested_call_module_success

theorem accepted_generated_closed_recursive_nested_call_module_nonTimeout_stop {cfg : Cfg} {fuel : Nat} {stop : Stop} {after : St}
    (accepted : Core.validate cfg.mod = .ok ())
    (initializers : ClosedGlobalInitializers cfg.mod)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : ∀ (state middle : St), NestedCallLoopStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := [(impl.body.scope, middle.nextScope)], depth := 1 } impl.body.stmts)
    (noValue : impl.body.value = none)
    (nonTimeout : stop ≠ .timeout)
    (run : GIR.runModule fuel ⟨cfg.profile, lower cfg.mod⟩ St.initial = .stop stop after) :
    ∃ sourceFuel, Core.runModule sourceFuel cfg St.initial = .stop stop after :=
  accepted_generated_recursive_nested_call_module_nonTimeout_stop accepted (closed_global_expression_reflection initializers) contextAt implAt fragment noValue nonTimeout run

#print axioms accepted_generated_closed_recursive_nested_call_module_nonTimeout_stop

#print axioms ClosedGlobalExpression.reflection
#print axioms closed_global_expression_reflection
end Goose.Lower

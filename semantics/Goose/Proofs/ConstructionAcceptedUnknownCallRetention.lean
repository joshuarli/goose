import Goose.Proofs.ConstructionAcceptedUnknownRetention
import Goose.Proofs.ConstructionAcceptedUnknownScalarArgument
import Goose.Proofs.ConstructionAcceptedParameterCallAccess
import Lean.Elab.Tactic

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private def callRetentionHelperName (name : String) : Lean.Name :=
  Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Roots") 0) "Goose") "Construct") name

elab "unfold_call_retention_checks" : tactic => do
  let scopedCheck := Lean.mkIdent (callRetentionHelperName "checkScopedShrinkAliases")
  let interior := Lean.mkIdent (callRetentionHelperName "interiorAliasType")
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $scopedCheck $interior at *))

theorem initializer_zeroCall_retains (config : EvalConfig) (names : Array (List RootRef)) (target : Nat)
    (context : Context) (callee : Impl) (before after : RState) (roots : List RootRef)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (prior : before.eff.unknown = true)
    (checked : rpCall (initializerSource config names) target [] before = .ok (roots, after)) :
    after.eff.unknown = true := by
  cases summary : callee.summary with
  | unknown => exact initializer_unknown_zeroCall config names target context callee before after roots contextAt calleeAt parameters summary checked
  | known value =>
    unfold rpCall at checked
    simp only [initializerSource, contextAt, calleeAt, parameters, summary] at checked
    unfold_call_retention_checks
    simp [initImpl, callEffects, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      modify, get, liftV, Goose.Core.forAll, getThe, modifyGet, MonadStateOf.get, MonadStateOf.modifyGet,
      StateT.get, StateT.modifyGet, summary] at checked
    cases result : callResultRoots callee context [] with
    | error failure => simp [result] at checked
    | ok resultValue =>
      simp [result] at checked
      obtain ⟨_, rfl⟩ := checked
      exact prior

theorem initializer_zeroCallExpr_retains (config : EvalConfig) (names : Array (List RootRef)) (target origin : Nat)
    (context : Context) (callee : Impl)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) : InitializerRetainsUnknown config names (.call target [] origin) := by
  intro before after roots prior checked
  simp only [rpExpr, rpArgs, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, initializerSource,
    contextAt, calleeAt, parameters] at checked
  simp [List.forIn_nil, liftV, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at checked
  cases contents : checkContents (initializerSource config names) target [] [] with
  | error failure =>
    simp only [initializerSource] at contents
    simp [contents] at checked
  | ok value =>
    simp only [initializerSource] at contents
    simp [contents] at checked
    exact initializer_zeroCall_retains config names target context callee before after roots contextAt calleeAt parameters prior checked

theorem initializer_scalarArgumentCall_retains (config : EvalConfig) (names : Array (List RootRef)) (target : Nat)
    (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (argumentRoots : List RootRef) (before after : RState) (roots : List RootRef)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (declared : callee.vars[parameter.var]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool) (prior : before.eff.unknown = true)
    (checked : rpCall (initializerSource config names) target [argumentRoots] before = .ok (roots, after)) :
    after.eff.unknown = true := by
  cases summary : callee.summary with
  | unknown =>
    exact initializer_unknown_scalarArgumentCall config names target context callee parameter descriptor argumentRoots before after roots
      contextAt calleeAt parameters declared scalar summary checked
  | known value =>
    rcases scalar with ⟨integer, scalar⟩ | scalar
    all_goals
      unfold rpCall at checked
      simp only [initializerSource, contextAt, calleeAt, parameters, summary] at checked
      unfold_call_retention_checks
      simp [initImpl, callEffects, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
        modify, get, liftV, Goose.Core.forAll, getThe, modifyGet, MonadStateOf.get, MonadStateOf.modifyGet,
        StateT.get, StateT.modifyGet, summary, declared, scalar] at checked
      cases argumentCheck : checkArgRoots callee context [argumentRoots] 0 with
      | error failure => simp [argumentCheck] at checked
      | ok checkedArgument =>
        simp [argumentCheck] at checked
        cases result : callResultRoots callee context [argumentRoots] with
        | error failure => simp [result] at checked
        | ok resultValue =>
          simp [result] at checked
          obtain ⟨_, rfl⟩ := checked
          exact prior

#print axioms initializer_scalarArgumentCall_retains

theorem initializer_scalarArgumentCallExpr_retains (config : EvalConfig) (names : Array (List RootRef)) (target origin : Nat)
    (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (argument : Expr) (before after : RState) (roots : List RootRef)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (declared : callee.vars[parameter.var]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool)
    (argumentRetains : InitializerRetainsUnknown config names argument) (prior : before.eff.unknown = true)
    (checked : rpExpr (initializerSource config names) (.call target [.byVal argument] origin) before = .ok (roots, after)) :
    after.eff.unknown = true := by
  simp only [rpExpr, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, initializerSource,
    contextAt, calleeAt, parameters] at checked
  cases argumentsChecked : rpArgs (initializerSource config names) [.byVal argument] before with
  | error failure =>
    simp only [initializerSource] at argumentsChecked
    simp [argumentsChecked] at checked
  | ok pair =>
    obtain ⟨argumentRoots, middle⟩ := pair
    cases operand : rpExpr (initializerSource config names) argument before with
    | error failure => simp [rpArgs, bind, StateT.bind, Except.bind, operand] at argumentsChecked
    | ok pair =>
      obtain ⟨operandRoots, operandAfter⟩ := pair
      have argumentUnknown := argumentRetains before operandAfter operandRoots prior operand
      have middleUnknown := (rpArgs_singleByValue_effectState operand argumentsChecked).2.2.trans argumentUnknown
      have same := rpArgs_singleByValue_roots operand argumentsChecked
      subst argumentRoots
      simp only [initializerSource] at argumentsChecked
      simp [argumentsChecked, List.forIn_cons, List.forIn_nil, liftV, pure, StateT.pure, Except.pure] at checked
      cases contents : checkContents (initializerSource config names) target [.byVal argument] [operandRoots] with
      | error failure =>
        simp only [initializerSource] at contents
        simp [contents, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at checked
      | ok value =>
        simp only [initializerSource] at contents
        simp [contents, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at checked
        exact initializer_scalarArgumentCall_retains config names target context callee parameter descriptor operandRoots middle after roots
          contextAt calleeAt parameters declared scalar middleUnknown checked

#print axioms initializer_scalarArgumentCallExpr_retains

inductive InitializerScalarWithCalls (config : EvalConfig) : Expr → Prop
  | scalar {expression : Expr} : AcceptedBinaryExpression expression → InitializerScalarWithCalls config expression
  | call (target origin : Nat) (context : Context) (callee : Impl) :
      config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some callee → callee.params = #[] →
      InitializerScalarWithCalls config (.call target [] origin)
  | scalarCall (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
      {argument : Expr} : config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some callee →
      callee.params = #[parameter] → callee.vars[parameter.var]? = some descriptor →
      ((∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool) → InitializerScalarWithCalls config argument →
      InitializerScalarWithCalls config (.call target [.byVal argument] origin)
  | unary (operation : Goose.Core.UnOp) (origin : Nat) {expression : Expr} :
      InitializerScalarWithCalls config expression → InitializerScalarWithCalls config (.un operation expression origin)
  | conversion (kind : Goose.Core.ConvKind) (ty : Ty) (origin : Nat) {expression : Expr} :
      InitializerScalarWithCalls config expression → InitializerScalarWithCalls config (.conv kind ty expression origin)
  | not {expression : Expr} : InitializerScalarWithCalls config expression → InitializerScalarWithCalls config (.not expression)
  | binary (operation : Goose.Core.BinOp) (origin : Nat) {left right : Expr} :
      InitializerScalarWithCalls config left → InitializerScalarWithCalls config right →
      InitializerScalarWithCalls config (.bin operation left right origin)
  | comparison (operation : Goose.Core.CmpOp) {left right : Expr} :
      InitializerScalarWithCalls config left → InitializerScalarWithCalls config right →
      InitializerScalarWithCalls config (.cmp operation left right)
  | conjunction {left right : Expr} : InitializerScalarWithCalls config left → InitializerScalarWithCalls config right →
      InitializerScalarWithCalls config (.and left right)
  | disjunction {left right : Expr} : InitializerScalarWithCalls config left → InitializerScalarWithCalls config right →
      InitializerScalarWithCalls config (.or left right)

theorem initializer_callScalar_retains (config : EvalConfig) (names : Array (List RootRef)) {expression : Expr}
    (form : InitializerScalarWithCalls config expression) : InitializerRetainsUnknown config names expression := by
  induction form with
  | scalar form => exact initializer_retains_binaryExpression form config names
  | call target origin context callee contextAt calleeAt parameters =>
    exact initializer_zeroCallExpr_retains config names target origin context callee contextAt calleeAt parameters
  | scalarCall target origin context callee parameter descriptor contextAt calleeAt parameters declared scalar argumentForm ih =>
    intro before after roots prior checked
    exact initializer_scalarArgumentCallExpr_retains config names target origin context callee parameter descriptor _ before after roots
      contextAt calleeAt parameters declared scalar ih prior checked
  | unary operation origin form ih => exact initializer_retains_unary config names operation _ origin ih
  | conversion kind ty origin form ih => exact initializer_retains_conversion config names kind ty _ origin ih
  | not form ih => exact initializer_retains_not config names _ ih
  | binary operation origin left right leftIH rightIH => exact initializer_retains_binary config names operation _ _ origin leftIH rightIH
  | comparison operation left right leftIH rightIH => exact initializer_retains_cmp config names operation _ _ leftIH rightIH
  | conjunction left right leftIH rightIH => exact initializer_retains_and config names _ _ leftIH rightIH
  | disjunction left right leftIH rightIH => exact initializer_retains_or config names _ _ leftIH rightIH

theorem validated_scalar_initializer_binaryLeftCalls_known (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (target origin : Nat) (context : Context) (callee : Impl)
    (operation : Goose.Core.BinOp) (left right : Expr) (location : Nat)
    (present : config.module.globals[id]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool)
    (expression : descriptor.init = .bin operation left right location)
    (leftForm : OperatorWrappedZeroCall target origin left) (rightForm : InitializerScalarWithCalls config right)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) : ∃ summary, callee.summary = .known summary := by
  obtain ⟨names, roots, after, rooted, clear⟩ := validated_scalar_initializer_noUnknown config accepted id descriptor present scalar
  rw [expression] at rooted
  cases summary : callee.summary with
  | known value => exact ⟨value, rfl⟩
  | unknown =>
    have leftUnknown := initializer_unknown_operatorWrappedZeroCall config names target origin context callee
      contextAt calleeAt parameters summary leftForm
    have retained := initializer_callScalar_retains config names rightForm
    have raised := initializer_unknown_binaryLeft config names operation left right location leftUnknown retained ⟨0, {}, []⟩ after roots rooted
    simp [clear] at raised

#print axioms initializer_callScalar_retains
#print axioms validated_scalar_initializer_binaryLeftCalls_known
#print axioms initializer_zeroCall_retains
#print axioms initializer_zeroCallExpr_retains
end Goose.Proofs.ConstructionAcceptedExecution

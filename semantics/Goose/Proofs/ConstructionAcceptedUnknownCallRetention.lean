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

theorem initializer_scalarArgumentCallExpr_fromArgument (config : EvalConfig) (names : Array (List RootRef)) (target origin : Nat)
    (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (argument : Expr) (before after : RState) (roots : List RootRef)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (declared : callee.vars[parameter.var]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool)
    (argumentUnknown : ∀ childRoots middle, rpExpr (initializerSource config names) argument before = .ok (childRoots, middle) →
      middle.eff.unknown = true)
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
      have argumentRaised := argumentUnknown operandRoots operandAfter operand
      have middleUnknown := (rpArgs_singleByValue_effectState operand argumentsChecked).2.2.trans argumentRaised
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


theorem initializer_scalarArgumentCallExpr_retains (config : EvalConfig) (names : Array (List RootRef)) (target origin : Nat)
    (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (argument : Expr) (before after : RState) (roots : List RootRef)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (declared : callee.vars[parameter.var]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool)
    (argumentRetains : InitializerRetainsUnknown config names argument) (prior : before.eff.unknown = true)
    (checked : rpExpr (initializerSource config names) (.call target [.byVal argument] origin) before = .ok (roots, after)) :
    after.eff.unknown = true := by
  exact initializer_scalarArgumentCallExpr_fromArgument config names target origin context callee parameter descriptor argument before after roots
    contextAt calleeAt parameters declared scalar (fun childRoots middle child => argumentRetains before middle childRoots prior child) checked

#print axioms initializer_scalarArgumentCallExpr_fromArgument
#print axioms initializer_scalarArgumentCallExpr_retains

inductive InitializerNestedCallPath (config : EvalConfig) (target origin : Nat) (arguments : List Arg) : Expr → Prop
  | call : InitializerNestedCallPath config target origin arguments (.call target arguments origin)
  | not {expression : Expr} : InitializerNestedCallPath config target origin arguments expression →
      InitializerNestedCallPath config target origin arguments (.not expression)
  | unary (operation : Goose.Core.UnOp) (location : Nat) {expression : Expr} :
      InitializerNestedCallPath config target origin arguments expression → InitializerNestedCallPath config target origin arguments (.un operation expression location)
  | conversion (kind : Goose.Core.ConvKind) (ty : Ty) (location : Nat) {expression : Expr} :
      InitializerNestedCallPath config target origin arguments expression → InitializerNestedCallPath config target origin arguments (.conv kind ty expression location)
  | binaryRight (operation : Goose.Core.BinOp) (left : Expr) (location : Nat) {right : Expr} :
      InitializerNestedCallPath config target origin arguments right → InitializerNestedCallPath config target origin arguments (.bin operation left right location)
  | compareRight (operation : Goose.Core.CmpOp) (left : Expr) {right : Expr} :
      InitializerNestedCallPath config target origin arguments right → InitializerNestedCallPath config target origin arguments (.cmp operation left right)
  | andRight (left : Expr) {right : Expr} : InitializerNestedCallPath config target origin arguments right →
      InitializerNestedCallPath config target origin arguments (.and left right)
  | orRight (left : Expr) {right : Expr} : InitializerNestedCallPath config target origin arguments right →
      InitializerNestedCallPath config target origin arguments (.or left right)
  | scalarArgument (outerTarget outerOrigin : Nat) (outerContext : Context) (outerCallee : Impl)
      (parameter : Param) (descriptor : LocalVar) {argument : Expr} :
      config.module.contexts[outerTarget]? = some outerContext → config.module.impls[outerContext.impl]? = some outerCallee →
      outerCallee.params = #[parameter] → outerCallee.vars[parameter.var]? = some descriptor →
      ((∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool) →
      InitializerNestedCallPath config target origin arguments argument →
      InitializerNestedCallPath config target origin arguments (.call outerTarget [.byVal argument] outerOrigin)

theorem initializer_unknown_nestedCallPath (config : EvalConfig) (names : Array (List RootRef)) (target origin : Nat)
    (arguments : List Arg) (context : Context) (callee : Impl) (contextAt : config.module.contexts[target]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee) (unknown : callee.summary = .unknown) :
    ∀ {expression}, InitializerNestedCallPath config target origin arguments expression → InitializerRaisesUnknown config names expression := by
  intro expression form
  induction form with
  | call =>
    intro before after roots checked
    exact initializer_unknown_anyArgumentCallExpr config names target origin context callee arguments before after roots contextAt calleeAt unknown checked
  | not inner ih =>
    intro before after roots checked
    exact initializer_unknown_not config names _ before after roots (fun childRoots middle child => ih before middle childRoots child) checked
  | unary operation location inner ih => exact initializer_unknown_unary config names operation _ location ih
  | conversion kind ty location inner ih => exact initializer_unknown_conversion config names kind ty _ location ih
  | binaryRight operation left location inner ih => exact initializer_unknown_binaryRight config names operation left _ location ih
  | compareRight operation left inner ih => exact initializer_unknown_cmpRight config names operation left _ ih
  | andRight left inner ih => exact initializer_unknown_andRight config names left _ ih
  | orRight left inner ih => exact initializer_unknown_orRight config names left _ ih
  | scalarArgument outerTarget outerOrigin outerContext outerCallee parameter descriptor outerContextAt outerCalleeAt parameters declared scalar inner ih =>
    intro before after roots checked
    exact initializer_scalarArgumentCallExpr_fromArgument config names outerTarget outerOrigin outerContext outerCallee parameter descriptor _ before after roots
      outerContextAt outerCalleeAt parameters declared scalar (fun childRoots middle child => ih before middle childRoots child) checked

theorem validated_scalar_initializer_nestedCallPath_known (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (global : Global) (target origin : Nat) (arguments : List Arg) (context : Context) (callee : Impl)
    (present : config.module.globals[id]? = some global) (scalar : (∃ integer, global.ty = .int integer) ∨ global.ty = .bool)
    (form : InitializerNestedCallPath config target origin arguments global.init)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee) :
    ∃ summary, callee.summary = .known summary := by
  obtain ⟨names, roots, after, rooted, clear⟩ := validated_scalar_initializer_noUnknown config accepted id global present scalar
  cases summary : callee.summary with
  | known value => exact ⟨value, rfl⟩
  | unknown =>
    have raised := initializer_unknown_nestedCallPath config names target origin arguments context callee contextAt calleeAt summary
      form ⟨0, {}, []⟩ after roots rooted
    simp [clear] at raised

#print axioms initializer_unknown_nestedCallPath
#print axioms validated_scalar_initializer_nestedCallPath_known

theorem OperatorWrappedCall.toNestedCallPath (config : EvalConfig) {target origin : Nat} {arguments : List Arg} {expression : Expr}
    (form : OperatorWrappedCall target origin arguments expression) : InitializerNestedCallPath config target origin arguments expression := by
  induction form with
  | call => exact .call
  | not inner ih => exact .not ih
  | unary operation location inner ih => exact .unary operation location ih
  | conversion kind ty location inner ih => exact .conversion kind ty location ih
  | binaryRight operation left location inner ih => exact .binaryRight operation left location ih
  | compareRight operation left inner ih => exact .compareRight operation left ih
  | andRight left inner ih => exact .andRight left ih
  | orRight left inner ih => exact .orRight left ih

#print axioms OperatorWrappedCall.toNestedCallPath

theorem validated_scalar_initializer_nestedArgument_known (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (global : Global) (outerTarget outerOrigin : Nat) (outerContext : Context) (outerCallee : Impl)
    (parameter : Param) (descriptor : LocalVar) (argument : Expr)
    (innerTarget innerOrigin : Nat) (innerArguments : List Arg) (innerContext : Context) (innerCallee : Impl)
    (present : config.module.globals[id]? = some global)
    (resultScalar : (∃ integer, global.ty = .int integer) ∨ global.ty = .bool)
    (expression : global.init = .call outerTarget [.byVal argument] outerOrigin)
    (outerContextAt : config.module.contexts[outerTarget]? = some outerContext)
    (outerCalleeAt : config.module.impls[outerContext.impl]? = some outerCallee)
    (parameters : outerCallee.params = #[parameter]) (declared : outerCallee.vars[parameter.var]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool)
    (form : OperatorWrappedCall innerTarget innerOrigin innerArguments argument)
    (innerContextAt : config.module.contexts[innerTarget]? = some innerContext)
    (innerCalleeAt : config.module.impls[innerContext.impl]? = some innerCallee) : ∃ summary, innerCallee.summary = .known summary := by
  apply validated_scalar_initializer_nestedCallPath_known config accepted id global innerTarget innerOrigin innerArguments innerContext innerCallee
    present resultScalar
  · rw [expression]
    exact .scalarArgument outerTarget outerOrigin outerContext outerCallee parameter descriptor outerContextAt outerCalleeAt parameters declared scalar
      (form.toNestedCallPath config)
  · exact innerContextAt
  · exact innerCalleeAt

#print axioms validated_scalar_initializer_nestedArgument_known

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

theorem validated_scalar_initializer_binaryLeftAnyCall_known (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (target origin : Nat) (arguments : List Arg) (context : Context) (callee : Impl)
    (operation : Goose.Core.BinOp) (left right : Expr) (location : Nat)
    (present : config.module.globals[id]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool)
    (expression : descriptor.init = .bin operation left right location)
    (leftForm : OperatorWrappedCall target origin arguments left) (rightForm : InitializerScalarWithCalls config right)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    : ∃ summary, callee.summary = .known summary := by
  obtain ⟨names, roots, after, rooted, clear⟩ := validated_scalar_initializer_noUnknown config accepted id descriptor present scalar
  rw [expression] at rooted
  cases summary : callee.summary with
  | known value => exact ⟨value, rfl⟩
  | unknown =>
    have leftUnknown := initializer_unknown_operatorWrappedCall config names target origin arguments context callee
      contextAt calleeAt summary leftForm
    have retained := initializer_callScalar_retains config names rightForm
    have raised := initializer_unknown_binaryLeft config names operation left right location leftUnknown retained ⟨0, {}, []⟩ after roots rooted
    simp [clear] at raised


theorem validated_scalar_initializer_binaryLeftCalls_known (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (target origin : Nat) (context : Context) (callee : Impl)
    (operation : Goose.Core.BinOp) (left right : Expr) (location : Nat)
    (present : config.module.globals[id]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool)
    (expression : descriptor.init = .bin operation left right location)
    (leftForm : OperatorWrappedZeroCall target origin left) (rightForm : InitializerScalarWithCalls config right)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) : ∃ summary, callee.summary = .known summary := by
  exact validated_scalar_initializer_binaryLeftAnyCall_known config accepted id descriptor target origin [] context callee operation left right
    location present scalar expression leftForm.toWrappedCall rightForm contextAt calleeAt

#print axioms initializer_callScalar_retains
#print axioms validated_scalar_initializer_binaryLeftAnyCall_known
#print axioms validated_scalar_initializer_binaryLeftCalls_known
#print axioms initializer_zeroCall_retains
#print axioms initializer_zeroCallExpr_retains
end Goose.Proofs.ConstructionAcceptedExecution

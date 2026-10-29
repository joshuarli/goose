import Goose.Proofs.ConstructionAcceptedUnknownCall
import Goose.Proofs.ConstructionAcceptedParameterArgumentRoots
import Lean.Elab.Tactic

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private def argumentHelperName (name : String) : Lean.Name :=
  Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Roots") 0) "Goose") "Construct") name

elab "unfold_argument_call_checks" : tactic => do
  let scopedCheck := Lean.mkIdent (argumentHelperName "checkScopedShrinkAliases")
  let interior := Lean.mkIdent (argumentHelperName "interiorAliasType")
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $scopedCheck $interior at *))

theorem initializer_unknown_scalarArgumentCall (config : EvalConfig) (names : Array (List RootRef)) (target : Nat)
    (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (argumentRoots : List RootRef) (before after : RState) (roots : List RootRef)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (declared : callee.vars[parameter.var]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool) (unknown : callee.summary = .unknown)
    (checked : rpCall (initializerSource config names) target [argumentRoots] before = .ok (roots, after)) :
    after.eff.unknown = true := by
  rcases scalar with ⟨integer, scalar⟩ | scalar
  all_goals
    unfold rpCall at checked
    simp only [initializerSource, contextAt, calleeAt, parameters, unknown, declared, scalar] at checked
    unfold_argument_call_checks
    simp [initImpl, callEffects, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      modify, get, liftV, Goose.Core.forAll, getThe, modifyGet, MonadStateOf.get, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet,
      unknown, declared, scalar] at checked
    cases argumentCheck : checkArgRoots callee context [argumentRoots] 0 with
    | error failure => simp [argumentCheck] at checked
    | ok value =>
      simp [argumentCheck] at checked
      cases result : callResultRoots callee context [argumentRoots] with
      | error failure => simp [result] at checked
      | ok value =>
        simp [result] at checked
        obtain ⟨_, rfl⟩ := checked
        rfl

theorem initializer_unknown_scalarArgumentCallExpr (config : EvalConfig) (names : Array (List RootRef)) (target origin : Nat)
    (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (argument : Expr) (before after : RState) (roots : List RootRef)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (declared : callee.vars[parameter.var]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool) (unknown : callee.summary = .unknown)
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
        exact initializer_unknown_scalarArgumentCall config names target context callee parameter descriptor operandRoots middle after roots
          contextAt calleeAt parameters declared scalar unknown checked

theorem validated_scalar_initializer_scalarArgumentCall_known (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (global : Global) (target origin : Nat) (context : Context) (callee : Impl)
    (parameter : Param) (descriptor : LocalVar) (argument : Expr)
    (present : config.module.globals[id]? = some global)
    (resultScalar : (∃ resultInteger, global.ty = .int resultInteger) ∨ global.ty = .bool)
    (expression : global.init = .call target [.byVal argument] origin)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (declared : callee.vars[parameter.var]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool) : ∃ summary, callee.summary = .known summary := by
  obtain ⟨names, roots, after, rooted, clear⟩ := validated_scalar_initializer_noUnknown config accepted id global present resultScalar
  rw [expression] at rooted
  cases summary : callee.summary with
  | known value => exact ⟨value, rfl⟩
  | unknown =>
    have raised := initializer_unknown_scalarArgumentCallExpr config names target origin context callee parameter descriptor argument
      ⟨0, {}, []⟩ after roots contextAt calleeAt parameters declared scalar summary rooted
    simp [clear] at raised

#print axioms validated_scalar_initializer_scalarArgumentCall_known
#print axioms initializer_unknown_scalarArgumentCallExpr
#print axioms initializer_unknown_scalarArgumentCall
end Goose.Proofs.ConstructionAcceptedExecution

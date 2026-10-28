import Goose.Proofs.ConstructionAcceptedEntryUnitTyping
import Goose.Proofs.ConstructionAcceptedScalarEntryWitness

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private theorem scalar_read_not_unit (fuel : Nat) (environment : TypingEnv) (place : Place)
    (before after : Nat) (typed : typeExpr fuel environment (.read place) before = .ok ([.unit], after)) : False := by
  cases fuel with
  | zero => change Except.error _ = Except.ok _ at typed; cases typed
  | succ fuel =>
    simp only [typeExpr, bind, StateT.bind] at typed
    cases placeType : typePlace fuel environment place before with
    | error failure => simp only [placeType, Except.bind] at typed; cases typed
    | ok result =>
      obtain ⟨⟨ty, binding, contents⟩, counter⟩ := result
      simp only [placeType, Except.bind] at typed
      cases ty <;> first
        | (change Except.error _ = Except.ok _ at typed; cases typed)
        | (split at typed <;> cases typed)

theorem scalarExpression_not_unit {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (environment : TypingEnv) (before after : Nat)
    (typed : typeExpr fuel environment expression before = .ok ([.unit], after)) : False := by
  cases form with
  | numeric form =>
    cases form with
    | scalar form =>
      cases form with
      | scalar form =>
        cases form with
        | integer type value => cases fuel <;> cases typed
        | boolean value => cases fuel <;> cases typed
        | globalRead id => exact scalar_read_not_unit fuel environment (.global id) before after typed
        | localRead id => exact scalar_read_not_unit fuel environment (.var id) before after typed
      | not form => have same := typeExpr_not_singleton fuel environment _ before after [.unit] typed; cases same
    | unary operation origin form =>
      cases fuel with
      | zero => cases typed
      | succ fuel => obtain ⟨integer, same, _⟩ := typeExpr_un_operand fuel environment operation _ origin before after .unit typed; cases same
    | conversion kind target origin form =>
      cases fuel with
      | zero => cases typed
      | succ fuel => obtain ⟨source, integer, _, same, _⟩ := typeExpr_conv_operand fuel environment kind target _ origin before after .unit typed; cases same
  | binary operation origin left right =>
    cases fuel with
    | zero => cases typed
    | succ fuel => obtain ⟨integer, middle, same, _, _⟩ := typeExpr_bin_operands fuel environment operation _ _ origin before after .unit typed; cases same
  | comparison operation left right => have same := typeExpr_comparison_singleton fuel environment _ _ operation before after [.unit] typed; cases same
  | conjunction left right => have same := typeExpr_booleanBinary_singleton fuel environment _ _ true before after [.unit] typed; cases same
  | disjunction left right => have same := typeExpr_booleanBinary_singleton fuel environment _ _ false before after [.unit] typed; cases same
  | not form => have same := typeExpr_not_singleton fuel environment _ before after [.unit] typed; cases same
  | unary operation origin form =>
    cases fuel with
    | zero => cases typed
    | succ fuel => obtain ⟨integer, same, _⟩ := typeExpr_un_operand fuel environment operation _ origin before after .unit typed; cases same
  | conversion kind target origin form =>
    cases fuel with
    | zero => cases typed
    | succ fuel => obtain ⟨source, integer, _, same, _⟩ := typeExpr_conv_operand fuel environment kind target _ origin before after .unit typed; cases same

theorem acceptedEntry_scalarTail_impossible (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl) (expression : Expr)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (tail : implementation.body.value = some expression) (form : AcceptedBinaryExpression expression) : False := by
  obtain ⟨entry, impl, entryAt, implAt, params, results⟩ := Goose.Proofs.ConstructionRootCorrespondence.validated_entry config.module accepted.accepted
  have sameEntry : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
  subst entry
  have sameImpl : impl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
  subst impl
  obtain ⟨declared, typed⟩ := validated_implementation_unit_typing config.module original.impl implementation
    accepted.accepted implementationAt results
  cases body : implementation.body with
  | mk scope statements value =>
    simp only [body, Block.value] at tail
    subst value
    rw [body] at typed
    simp only [Block.scope, typeBlock, bind, StateT.bind] at typed
    cases statementsTyped : typeStatements 4095
        { module := config.module, implementation := some implementation, variables := implementation.vars,
          visible := List.range implementation.params.size, scope := scope, loops := 0,
          use := if implementation.results.isEmpty then .ordinary else .result, request := .value,
          resultRequests := implementation.results.toList.map (·.request), globalLimit := config.module.globals.size }
        statements implementation.params.size with
    | error failure => rw [statementsTyped] at typed; cases typed
    | ok result =>
      obtain ⟨environment, counter⟩ := result
      rw [statementsTyped] at typed
      exact scalarExpression_not_unit form 4095 environment counter declared typed

#print axioms acceptedEntry_scalarTail_impossible
#print axioms scalarExpression_not_unit
end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionAcceptedScalarLocalTyping
import Goose.Proofs.ConstructionAcceptedParameterSource

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem typeArguments_twoScalar_operands (fuel : Nat) (environment : TypingEnv) (callee : Impl)
    (first second : Param) (firstDescriptor secondDescriptor : LocalVar) (left right : Expr) (before after : Nat)
    (firstMode : first.mode = .byValue) (secondMode : second.mode = .byValue)
    (firstDeclared : callee.vars[first.var]? = some firstDescriptor)
    (secondDeclared : callee.vars[second.var]? = some secondDescriptor)
    (checked : typeArguments (fuel + 2) environment callee [first, second] [.byVal left, .byVal right] before = .ok ((), after)) :
    ∃ firstTy firstAfter secondTy secondAfter,
      typeExpr (fuel + 1) { environment with use := .ordinary, request := .value, resultRequests := [] } left before = .ok ([firstTy], firstAfter) ∧
      firstTy.passesTo firstDescriptor.ty = true ∧
      typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] } right firstAfter = .ok ([secondTy], secondAfter) ∧
      secondTy.passesTo secondDescriptor.ty = true := by
  simp only [typeArguments, firstDeclared, firstMode, bind, StateT.bind] at checked
  cases nonfixed : firstDescriptor.ty.nonfixed with
  | true =>
    simp only [nonfixed] at checked
    change Except.error _ = Except.ok _ at checked
    cases checked
  | false =>
    simp only [nonfixed] at checked
    change (typeExpr (fuel + 1) { environment with use := .ordinary, request := .value, resultRequests := [] } left before).bind _ = _ at checked
    cases operand : typeExpr (fuel + 1) { environment with use := .ordinary, request := .value, resultRequests := [] } left before with
    | error failure => simp only [operand, Except.bind] at checked; cases checked
    | ok result =>
      obtain ⟨types, firstAfter⟩ := result
      simp only [operand, Except.bind] at checked
      cases types with
      | nil => change Except.error _ = Except.ok _ at checked; cases checked
      | cons firstTy rest =>
        cases rest with
        | cons other remaining => change Except.error _ = Except.ok _ at checked; cases checked
        | nil =>
          unfold_scalar_typing_helpers
          cases passes : firstTy.passesTo firstDescriptor.ty with
          | false =>
            simp only [pure, StateT.pure, Except.pure, passes, Bool.false_eq_true, ↓reduceIte] at checked
            change Except.error _ = Except.ok _ at checked
            cases checked
          | true =>
            simp only [pure, StateT.pure, Except.pure, passes, ↓reduceIte] at checked
            have tail : typeArguments (fuel + 1) environment callee [second] [.byVal right] firstAfter = .ok ((), after) := by
              simp only [typeArguments]
              unfold_scalar_typing_helpers
              exact checked
            obtain ⟨secondTy, secondAfter, rightTyped, secondPasses⟩ :=
              typeArguments_scalar_operand fuel environment callee second secondDescriptor right firstAfter after
                secondMode secondDeclared tail
            exact ⟨firstTy, firstAfter, secondTy, secondAfter, rfl, passes, rightTyped, secondPasses⟩

theorem typeExpr_twoScalarCall_operands (fuel : Nat) (environment : TypingEnv) (contextId origin : Nat)
    (context : Context) (callee : Impl) (first second : Param) (firstDescriptor secondDescriptor : LocalVar)
    (left right : Expr) (before after : Nat) (resultTypes : List Ty)
    (contextAt : environment.module.contexts[contextId]? = some context)
    (calleeAt : environment.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[first, second])
    (firstMode : first.mode = .byValue) (secondMode : second.mode = .byValue)
    (firstDeclared : callee.vars[first.var]? = some firstDescriptor)
    (secondDeclared : callee.vars[second.var]? = some secondDescriptor)
    (firstScalar : (∃ intTy, firstDescriptor.ty = .int intTy) ∨ firstDescriptor.ty = .bool)
    (secondScalar : (∃ intTy, secondDescriptor.ty = .int intTy) ∨ secondDescriptor.ty = .bool)
    (checked : typeExpr (fuel + 3) environment (.call contextId [.byVal left, .byVal right] origin) before = .ok (resultTypes, after)) :
    ∃ firstAfter secondAfter,
      typeExpr (fuel + 1) { environment with use := .ordinary, request := .value, resultRequests := [] } left before =
        .ok ([firstDescriptor.ty], firstAfter) ∧
      typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] } right firstAfter =
        .ok ([secondDescriptor.ty], secondAfter) := by
  obtain ⟨middle, arguments⟩ := typeExpr_call_arguments (fuel + 2) environment contextId context callee
    [.byVal left, .byVal right] origin before after resultTypes contextAt calleeAt checked
  have argumentCheck : typeArguments (fuel + 2) environment callee [first, second] [.byVal left, .byVal right] before = .ok ((), middle) := by
    simpa [parameters] using arguments
  obtain ⟨firstTy, firstAfter, secondTy, secondAfter, firstTyped, firstPasses, secondTyped, secondPasses⟩ :=
    typeArguments_twoScalar_operands fuel environment callee first second firstDescriptor secondDescriptor left right before middle
      firstMode secondMode firstDeclared secondDeclared argumentCheck
  have firstEq := scalarParameter_passesTo_eq firstTy firstDescriptor.ty firstScalar firstPasses
  have secondEq := scalarParameter_passesTo_eq secondTy secondDescriptor.ty secondScalar secondPasses
  subst firstTy secondTy
  exact ⟨firstAfter, secondAfter, firstTyped, secondTyped⟩

#print axioms typeExpr_twoScalarCall_operands
#print axioms typeArguments_twoScalar_operands
end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionAcceptedTwoArgumentTyping

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem typeArguments_scalarByValue_cons (fuel : Nat) (environment : TypingEnv) (callee : Impl)
    (parameter : Param) (descriptor : LocalVar) (parameters : List Param) (expression : Expr) (arguments : List Arg)
    (before after : Nat) (mode : parameter.mode = .byValue) (declared : callee.vars[parameter.var]? = some descriptor)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (checked : typeArguments (fuel + 1) environment callee (parameter :: parameters) (.byVal expression :: arguments) before = .ok ((), after)) :
    ∃ middle, typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
        expression before = .ok ([descriptor.ty], middle) ∧
      typeArguments fuel environment callee parameters arguments middle = .ok ((), after) := by
  simp only [typeArguments, declared, mode, bind, StateT.bind] at checked
  cases nonfixed : descriptor.ty.nonfixed with
  | true =>
    simp only [nonfixed] at checked
    change Except.error _ = Except.ok _ at checked
    cases checked
  | false =>
    simp only [nonfixed] at checked
    change (typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] } expression before).bind _ = _ at checked
    cases operand : typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] } expression before with
    | error failure => simp only [operand, Except.bind] at checked; cases checked
    | ok result =>
      obtain ⟨types, middle⟩ := result
      simp only [operand, Except.bind] at checked
      cases types with
      | nil => change Except.error _ = Except.ok _ at checked; cases checked
      | cons expressionTy rest =>
        cases rest with
        | cons other remaining => change Except.error _ = Except.ok _ at checked; cases checked
        | nil =>
          unfold_scalar_typing_helpers
          cases passes : expressionTy.passesTo descriptor.ty with
          | false =>
            simp only [pure, StateT.pure, Except.pure, passes, Bool.false_eq_true, ↓reduceIte] at checked
            change Except.error _ = Except.ok _ at checked
            cases checked
          | true =>
            simp only [pure, StateT.pure, Except.pure, passes, ↓reduceIte] at checked
            have equal := scalarParameter_passesTo_eq expressionTy descriptor.ty scalar passes
            subst expressionTy
            refine ⟨middle, rfl, ?_⟩
            simpa only [typeArguments] using checked

#print axioms typeArguments_scalarByValue_cons
end Goose.Proofs.ConstructionAcceptedExecution

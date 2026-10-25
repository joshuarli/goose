import Goose.Proofs.ConstructionAcceptedValues

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

def ordinaryOperandFrame (frame : ConstructionSourceFrame) (fuel : Nat) : ConstructionSourceFrame :=
  { frame with
    typingFuel := fuel
    typing := { frame.typing with use := .ordinary, request := .value, resultRequests := [] } }

theorem rpExpr_not_operand (environment : PEnv) (expression : Expr) (before after : RState)
    (roots : List RootRef) (checked : (rpExpr environment (.not expression)).run before = .ok (roots, after)) :
    roots = [] ∧ ∃ operandRoots, (rpExpr environment expression).run before = .ok (operandRoots, after) := by
  change (Except.bind (rpExpr environment expression before) fun result =>
    .ok ([], result.2)) = .ok (roots, after) at checked
  cases operand : rpExpr environment expression before with
  | error failure => simp only [operand, Except.bind] at checked; cases checked
  | ok result =>
    obtain ⟨operandRoots, next⟩ := result
    simp only [operand, Except.bind] at checked
    cases checked
    exact ⟨rfl, operandRoots, operand⟩

theorem typeExpr_not_operand (fuel : Nat) (environment : TypingEnv) (expression : Expr)
    (before after : Nat) (ty : Ty)
    (checked : typeExpr (fuel + 1) environment (.not expression) before = .ok ([ty], after)) :
    ty = .bool ∧ typeExpr fuel
      { environment with use := .ordinary, request := .value, resultRequests := [] }
      expression before = .ok ([.bool], after) := by
  simp only [typeExpr, bind, StateT.bind] at checked
  change (Except.bind (typeExpr fuel
      { environment with use := .ordinary, request := .value, resultRequests := [] }
      expression before) _) = .ok ([ty], after) at checked
  generalize operand : typeExpr fuel
      { environment with use := .ordinary, request := .value, resultRequests := [] }
      expression before = result at checked
  cases result with
  | error failure => simp only [Except.bind] at checked; cases checked
  | ok result =>
    obtain ⟨types, next⟩ := result
    cases types with
    | nil =>
      change Except.error _ = Except.ok _ at checked
      cases checked
    | cons head tail =>
      cases tail with
      | cons second rest =>
        change Except.error _ = Except.ok _ at checked
        cases checked
      | nil =>
        cases head <;> first
        | change Except.error _ = Except.ok _ at checked
          cases checked
        | change Except.ok ([Ty.bool], next) = Except.ok ([ty], after) at checked
          cases checked
          exact ⟨rfl, rfl⟩

theorem checkedValue_not_operand (frame : ConstructionSourceFrame) (fuel : Nat)
    (expression : Expr) (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (fuelAt : frame.typingFuel = fuel + 1)
    (checked : CheckedValue frame (.not expression) ty roots typingAfter rootsAfter) :
    ty = .bool ∧ roots = [] ∧ ∃ operandRoots,
      CheckedValue (ordinaryOperandFrame frame fuel) expression .bool operandRoots typingAfter rootsAfter := by
  have typing := checked.typing
  rw [fuelAt] at typing
  obtain ⟨type, operandTyping⟩ := typeExpr_not_operand fuel frame.typing expression
    frame.typingCounter typingAfter ty typing
  obtain ⟨empty, operandRoots, operandProvenance⟩ := rpExpr_not_operand frame.source expression
    frame.rootCursor rootsAfter roots checked.provenance
  exact ⟨type, empty, operandRoots, operandTyping, operandProvenance, checked.available⟩

theorem evalValue_not_of_operand (fuel : Nat) (config : EvalConfig) (frame : ConstructionSourceFrame)
    (types : RootTypes) (before after : ExecutionState) (expression : Expr) (roots : List RootRef)
    (value : Value)
    (evaluated : evalValue fuel config frame.interpretation.environment expression before = .ok value after)
    (accepted : AcceptedValue config.layout types frame.interpretation after .bool roots value) :
    ∃ result, evalValue (fuel + 1) config frame.interpretation.environment (.not expression) before =
      .ok (.bool result) after ∧
      AcceptedValue config.layout types frame.interpretation after .bool [] (.bool result) := by
  cases represented : accepted.represented with
  | boolean value =>
    exact ⟨!value, by simp only [evalValue, evaluated, bind, expectBool, pure],
      acceptedValue_boolean config.layout types frame.interpretation after (!value)⟩
  | stored => contradiction

#print axioms rpExpr_not_operand
#print axioms typeExpr_not_operand
#print axioms checkedValue_not_operand
#print axioms evalValue_not_of_operand

end Goose.Proofs.ConstructionAcceptedExecution

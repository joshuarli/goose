import Goose.Proofs.ConstructionAcceptedScalarComplete

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

def CheckedExpressionEvaluation (expression : Expr) : Prop :=
  ∀ (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (_world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (_source : AcceptedFrame config accepted frame state types) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState), CheckedValue frame expression ty roots typingAfter rootsAfter →
    let outcome := evalValue fuel config frame.interpretation.environment expression state
    Goose.Proofs.Exit.stepState outcome = state ∧
      (∀ value after, outcome = .ok value after → AcceptedValue config.layout types frame.interpretation after ty roots value) ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types

theorem checkedExpressionEvaluation_not (expression : Expr) (operandComplete : CheckedExpressionEvaluation expression) : CheckedExpressionEvaluation (.not expression) := by
  intro fuel config accepted frame state ambient types live regions pending world source ty roots typingAfter rootsAfter checked
  cases typingFuel : frame.typingFuel with
  | zero =>
    have typing := checked.typing
    rw [typingFuel] at typing
    change Except.error _ = Except.ok _ at typing
    cases typing
  | succ n =>
    obtain ⟨sameTy, sameRoots, operandRoots, operandChecked⟩ :=
      checkedValue_not_operand frame n expression ty roots typingAfter rootsAfter typingFuel checked
    subst ty roots
    let child := ordinaryOperandFrame frame n
    have childSource := ordinaryOperandFrame_accepted accepted frame n state types source
    cases fuel with
    | zero => simp [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      have childResult := operandComplete fuel config accepted child state ambient types live regions pending world childSource .bool operandRoots typingAfter rootsAfter operandChecked
      change Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment expression state) = state ∧
        (∀ value after, evalValue fuel config frame.interpretation.environment expression state = .ok value after →
          AcceptedValue config.layout types frame.interpretation after .bool operandRoots value) ∧ _ at childResult
      cases evaluated : evalValue fuel config frame.interpretation.environment expression state with
      | stop reason after =>
        simp only [evaluated, Goose.Proofs.Exit.stepState] at childResult
        have same := childResult.1
        subst after
        simp only [evalValue, evaluated, bind, Goose.Proofs.Exit.stepState, reduceCtorEq, true_and]
        exact ⟨fun _ _ impossible => False.elim impossible, world, source⟩
      | escape address carriers after =>
        simp only [evaluated, Goose.Proofs.Exit.stepState] at childResult
        have same := childResult.1
        subst after
        simp only [evalValue, evaluated, bind, Goose.Proofs.Exit.stepState, reduceCtorEq, true_and]
        exact ⟨fun _ _ impossible => False.elim impossible, world, source⟩
      | jump target kind after =>
        simp only [evaluated, Goose.Proofs.Exit.stepState] at childResult
        have same := childResult.1
        subst after
        simp only [evalValue, evaluated, bind, Goose.Proofs.Exit.stepState, reduceCtorEq, true_and]
        exact ⟨fun _ _ impossible => False.elim impossible, world, source⟩
      | ok value after =>
        have childAccepted := childResult.2.1 value after evaluated
        simp only [evaluated, Goose.Proofs.Exit.stepState] at childResult
        have same := childResult.1
        subst after
        obtain ⟨result, completed, valid⟩ := evalValue_not_of_operand fuel config frame types state state expression operandRoots value
          evaluated childAccepted
        simp only [completed, Goose.Proofs.Exit.stepState, ExecutionStep.ok.injEq, true_and]
        refine ⟨?_, world, source⟩
        intro output after same
        obtain ⟨rfl, rfl⟩ := same
        exact valid


inductive AcceptedNotExpression : Expr → Prop
  | scalar {expression : Expr} : AcceptedScalarExpression expression → AcceptedNotExpression expression
  | not {expression : Expr} : AcceptedNotExpression expression → AcceptedNotExpression (.not expression)

theorem evalValue_checked_not_complete {expression : Expr} (form : AcceptedNotExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState) (checked : CheckedValue frame expression ty roots typingAfter rootsAfter) :
    let outcome := evalValue fuel config frame.interpretation.environment expression state
    Goose.Proofs.Exit.stepState outcome = state ∧
      (∀ value after, outcome = .ok value after → AcceptedValue config.layout types frame.interpretation after ty roots value) ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types := by
  induction form generalizing fuel config accepted frame state ambient types live regions pending ty roots typingAfter rootsAfter with
  | scalar form =>
    exact evalValue_checked_scalar_complete form fuel config accepted frame state ambient types live regions pending world source
      ty roots typingAfter rootsAfter checked
  | @not expression form ih =>
    have operand : CheckedExpressionEvaluation expression := by
      intro fuel config accepted frame state ambient types live regions pending world source ty roots typingAfter rootsAfter checked
      exact ih fuel config accepted frame state ambient types live regions pending world source ty roots typingAfter rootsAfter checked
    exact checkedExpressionEvaluation_not expression operand fuel config accepted frame state ambient types live regions pending world source
      ty roots typingAfter rootsAfter checked

#print axioms checkedExpressionEvaluation_not
#print axioms evalValue_checked_not_complete
end Goose.Proofs.ConstructionAcceptedExecution

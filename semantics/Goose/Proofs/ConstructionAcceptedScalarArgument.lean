import Goose.Proofs.ConstructionAcceptedScalarControl

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem evalArguments_checkedScalar_world {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (parameterVars : Array LocalVar) (parameter : Param)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState) (checked : CheckedValue frame expression ty roots typingAfter rootsAfter) :
    let outcome := evalArguments fuel config frame.interpretation.environment parameterVars [parameter] [.byVal expression] state
    Goose.Proofs.Exit.stepState outcome = state ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types ∧
      (match outcome with
      | .ok values after => ∃ value, values = [value] ∧ AcceptedValue config.layout types frame.interpretation after ty roots value
      | .stop .. => True
      | _ => False) := by
  cases fuel with
  | zero => simp [evalArguments, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
  | succ fuel =>
    have result := evalValue_checked_binary_recursive form fuel config accepted frame state ambient types live regions pending
      world source ty roots typingAfter rootsAfter checked
    have control := evalValue_scalar_controlFree form fuel config frame.interpretation.environment
    cases evaluated : evalValue fuel config frame.interpretation.environment expression state with
    | escape address carriers after => exact False.elim (control.1 state address carriers after evaluated)
    | jump target kind after => exact False.elim (control.2 state target kind after evaluated)
    | stop reason after =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at result
      have same := result.1
      subst after
      simp [evalArguments, evaluated, bind, Goose.Proofs.Exit.stepState, world, source]
    | ok value after =>
      have valid := result.2.1 value after evaluated
      simp only [evaluated, Goose.Proofs.Exit.stepState] at result
      have same := result.1
      subst after
      cases fuel with
      | zero => simp [evalArguments, evaluated, bind, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
      | succ fuel =>
        simp only [evalArguments, evaluated, bind, pure, Goose.Proofs.Exit.stepState]
        exact ⟨trivial, world, source, value, rfl, valid⟩

#print axioms evalArguments_checkedScalar_world
end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionAcceptedScalarArgument
import Goose.Proofs.ConstructionScalarTwoArgumentRuntime

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

def FirstArgumentOutcome (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (ty : Ty) (roots : List RootRef)
    (step : ExecutionStep Value) : Prop :=
  AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState step) ambient types live regions pending ∧
  AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState step) types ∧
  match step with
  | .ok value after => AcceptedValue config.layout types frame.interpretation after ty roots value
  | .stop .. => True
  | _ => False

theorem evalArguments_two_scalarOutcome {left right : Expr} (rightForm : AcceptedBinaryExpression right)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (variables : Array LocalVar) (first second : Param)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (firstTy secondTy : Ty) (firstRoots secondRoots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame right secondTy secondRoots typingAfter rootsAfter)
    (firstSafe : ∀ fuel, FirstArgumentOutcome config accepted frame ambient types live regions pending firstTy firstRoots
      (evalValue fuel config frame.interpretation.environment left state)) :
    let result := evalArguments fuel config frame.interpretation.environment variables [first, second] [.byVal left, .byVal right] state
    AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState result) ambient types live regions pending ∧
    AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState result) types ∧
    match result with
    | .ok values after => ∃ leftValue rightValue, values = [leftValue, rightValue] ∧
        AcceptedValue config.layout types frame.interpretation after firstTy firstRoots leftValue ∧
        AcceptedValue config.layout types frame.interpretation after secondTy secondRoots rightValue
    | .stop .. => True
    | _ => False := by
  cases fuel with
  | zero => simp [evalArguments, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
  | succ fuel =>
    cases fuel with
    | zero => simp [evalArguments, evalValue, bind, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      rw [evalArguments_twoByValue]
      have safe := firstSafe (fuel + 1)
      cases firstStep : evalValue (fuel + 1) config frame.interpretation.environment left state with
      | stop reason after =>
        simpa [firstStep, FirstArgumentOutcome, Goose.Proofs.Exit.stepState, bind] using safe
      | escape address carriers after | jump target kind after =>
        simp [firstStep, FirstArgumentOutcome] at safe
      | ok leftValue middle =>
        simp only [firstStep, FirstArgumentOutcome, Goose.Proofs.Exit.stepState] at safe
        have rightSafe := evalValue_checked_binary_recursive rightForm fuel config accepted frame middle ambient types live regions pending
          safe.1 safe.2.1 secondTy secondRoots typingAfter rootsAfter checked
        have control := evalValue_scalar_controlFree rightForm fuel config frame.interpretation.environment
        cases secondStep : evalValue fuel config frame.interpretation.environment right middle with
        | escape address carriers after => exact False.elim (control.1 middle address carriers after secondStep)
        | jump target kind after => exact False.elim (control.2 middle target kind after secondStep)
        | stop reason after =>
          simp only [secondStep, Goose.Proofs.Exit.stepState] at rightSafe
          have same := rightSafe.1
          subst after
          simp [firstStep, secondStep, bind, Goose.Proofs.Exit.stepState, safe.1, safe.2.1]
        | ok rightValue after =>
          have valid := rightSafe.2.1 rightValue after secondStep
          simp only [secondStep, Goose.Proofs.Exit.stepState] at rightSafe
          have same := rightSafe.1
          subst after
          cases fuel with
          | zero => simp [firstStep, secondStep, bind, evalArguments, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, safe.1, safe.2.1]
          | succ fuel =>
            simp only [firstStep, secondStep, bind, pure, evalArguments, Goose.Proofs.Exit.stepState]
            exact ⟨safe.1, safe.2.1, leftValue, rightValue, rfl, safe.2.2, valid⟩

#print axioms evalArguments_two_scalarOutcome
end Goose.Proofs.ConstructionAcceptedExecution

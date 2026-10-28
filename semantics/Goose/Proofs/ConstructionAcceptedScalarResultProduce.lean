import Goose.Proofs.ConstructionAcceptedRegisterTail
import Goose.Proofs.ConstructionAcceptedScalarArgument
import Goose.Proofs.ConstructionAcceptedRegisterCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem withCompletion_register_scalar {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation) (ty : Ty) (state : ExecutionState) :
    withCompletionChannels [.register ty] (expressionOrigin expression)
      (fun channels => evalProduce (fuel + 1) config environment channels expression) state =
      (do let value ← evalValue fuel config environment expression; pure [Carrier.register value]) state := by
  exact completion_register_scalar form fuel config environment state ty

theorem evalProduce_checkedScalar_register_world {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState) (checked : CheckedValue frame expression ty roots typingAfter rootsAfter) :
    let outcome := withCompletionChannels [.register ty] (expressionOrigin expression)
      (fun channels => evalProduce (fuel + 1) config frame.interpretation.environment channels expression) state
    Goose.Proofs.Exit.stepState outcome = state ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types ∧
      (match outcome with
      | .ok carriers after => ∃ value, carriers = [.register value] ∧ AcceptedValue config.layout types frame.interpretation after ty roots value
      | .stop .. => True
      | _ => False) := by
  have result := evalValue_checked_binary_recursive form fuel config accepted frame state ambient types live regions pending
    world source ty roots typingAfter rootsAfter checked
  have control := evalValue_scalar_controlFree form fuel config frame.interpretation.environment
  rw [withCompletion_register_scalar form fuel config frame.interpretation.environment ty state]
  cases evaluated : evalValue fuel config frame.interpretation.environment expression state with
  | escape address carriers after => exact False.elim (control.1 state address carriers after evaluated)
  | jump target kind after => exact False.elim (control.2 state target kind after evaluated)
  | stop reason after =>
    simp only [evaluated, Goose.Proofs.Exit.stepState] at result
    have same := result.1
    subst after
    simp [evaluated, bind, Goose.Proofs.Exit.stepState, world, source]
  | ok value after =>
    have valid := result.2.1 value after evaluated
    simp only [evaluated, Goose.Proofs.Exit.stepState] at result
    have same := result.1
    subst after
    simp only [evaluated, bind, pure, Goose.Proofs.Exit.stepState]
    exact ⟨trivial, world, source, value, rfl, valid⟩

#print axioms evalProduce_checkedScalar_register_world
#print axioms withCompletion_register_scalar
end Goose.Proofs.ConstructionAcceptedExecution

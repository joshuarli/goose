import Goose.Proofs.ConstructionAcceptedEarlierCallerObservations
import Goose.Proofs.ConstructionAcceptedNumericComplete
import Goose.Proofs.ConstructionAcceptedScalarControl

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem evalValue_checkedBinary_earlier {expression : Expr} (config : EvalConfig) (integer : Goose.Core.IntTy)
    (form : AcceptedBinaryExpression expression) (fuel : Nat) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame expression (.int integer) roots typingAfter rootsAfter) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := evalValue fuel config frame.interpretation.environment expression before
      RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations before.nextAct before (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok value _ => nextAmbient = ambient ∧ ValueRepresentation (.int integer) value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  have complete := evalValue_checked_binary_recursive form fuel config accepted frame before ambient types live regions pending
    world source (.int integer) roots typingAfter rootsAfter checked
  have control := evalValue_scalar_controlFree form fuel config frame.interpretation.environment
  cases evaluated : evalValue fuel config frame.interpretation.environment expression before with
  | stop reason after =>
    simp only [evaluated, Goose.Proofs.Exit.stepState] at complete
    have same := complete.1
    subst after
    exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source,
      source.futureGlobals, EarlierCallerObservations.refl _ _ _, trivial⟩
  | escape target carriers after => exact False.elim (control.1 before target carriers after evaluated)
  | jump target kind after => exact False.elim (control.2 before target kind after evaluated)
  | ok value after =>
    have acceptedValue := complete.2.1 value after evaluated
    simp only [evaluated, Goose.Proofs.Exit.stepState] at complete
    have same := complete.1
    subst after
    exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source,
      source.futureGlobals, EarlierCallerObservations.refl _ _ _, rfl, acceptedValue.represented⟩

#print axioms evalValue_checkedBinary_earlier
end Goose.Proofs.ConstructionAcceptedExecution

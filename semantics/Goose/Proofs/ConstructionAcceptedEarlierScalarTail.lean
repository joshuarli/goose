import Goose.Proofs.ConstructionAcceptedRegisterTail
import Goose.Proofs.ConstructionAcceptedEarlierCallerObservations

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execActivationBody_scalarTail_earlierObservations {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt) (before middle : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (ty : Ty) (frontier : Nat)
    (frontierBound : frontier ≤ activation.act) (channels : activation.channels = [.register ty])
    (environment : frame.interpretation.environment =
      { activation with scopes := (scope, before.nextScope) :: activation.scopes })
    (normal : execStmts (fuel + 1) config frame.interpretation.environment statements
      (ownershipResultScopeState activation scope before) = .ok (.normal .unit) middle)
    (world : AcceptedWorld config frame.initialized middle ambient types live regions pending)
    (source : AcceptedFrame config accepted frame middle types) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState) (checked : CheckedValue frame expression ty roots typingAfter rootsAfter) :
    EarlierCallerObservations frontier middle
      (Goose.Proofs.Exit.stepState (execActivationBody (fuel + 2) config activation [] ⟨scope, statements, some expression⟩ before))
      types types := by
  have result := evalValue_checked_binary_recursive form fuel config accepted frame middle ambient types live regions pending
    world source ty roots typingAfter rootsAfter checked
  have normal' : execStmts (fuel + 1) config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements
      (ownershipResultScopeState activation scope before) = .ok (.normal .unit) middle := by
    simpa only [environment] using normal
  have execution := execActivationBody_register_scalar_tail form fuel config activation scope statements before middle ty channels normal'
  rw [← environment] at execution
  rw [execution]
  cases evaluated : evalValue fuel config frame.interpretation.environment expression middle with
  | stop reason after =>
    simp only [evaluated, Goose.Proofs.Exit.stepState] at result
    have same := result.1
    subst after
    exact EarlierCallerObservations.refl frontier middle types
  | ok value after | escape address carriers after | jump destination kind after =>
    simp only [evaluated, Goose.Proofs.Exit.stepState] at result
    have same := result.1
    subst after
    exact EarlierCallerObservations.releaseScope frontier activation scope before.nextScope middle types frontierBound

#print axioms execActivationBody_scalarTail_earlierObservations
end Goose.Proofs.ConstructionAcceptedExecution

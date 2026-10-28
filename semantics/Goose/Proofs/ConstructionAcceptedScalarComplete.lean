import Goose.Proofs.ConstructionAcceptedCursor
import Goose.Proofs.ConstructionByteValueComplete

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

inductive AcceptedScalarExpression : Expr → Prop
  | integer (type : Goose.Core.IntTy) (value : Int) : AcceptedScalarExpression (.lit type value)
  | boolean (value : Bool) : AcceptedScalarExpression (.bool value)
  | globalRead (id : Nat) : AcceptedScalarExpression (.read (.global id))

theorem evalValue_checked_scalar_complete {expression : Expr} (form : AcceptedScalarExpression expression)
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
  have result : Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment expression state) = state ∧
      (∀ value after, evalValue fuel config frame.interpretation.environment expression state = .ok value after →
        AcceptedValue config.layout types frame.interpretation after ty roots value) := by
    cases form with
    | integer type number =>
      cases fuel with
      | zero => simp [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      | succ fuel =>
        obtain ⟨evaluated, valid⟩ := evalValue_checked_integer fuel config frame state types type number ty roots typingAfter rootsAfter checked
        simp only [evaluated, Goose.Proofs.Exit.stepState, ExecutionStep.ok.injEq, true_and]
        intro value after ⟨sameValue, sameState⟩
        subst value after
        exact valid
    | boolean value =>
      cases fuel with
      | zero => simp [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      | succ fuel =>
        obtain ⟨evaluated, valid⟩ := evalValue_checked_boolean fuel config frame state types value ty roots typingAfter rootsAfter checked
        simp only [evaluated, Goose.Proofs.Exit.stepState, ExecutionStep.ok.injEq, true_and]
        intro result after ⟨sameValue, sameState⟩
        subst result after
        exact valid
    | globalRead id =>
      cases fuel with
      | zero => simp [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      | succ fuel =>
        cases fuel with
        | zero => simp [evalValue, evalPlace, timeout, EvalM.stop, bind, Goose.Proofs.Exit.stepState]
        | succ fuel =>
          obtain ⟨value, evaluated, valid⟩ := evalValue_checkedGlobalRead_accepted fuel config accepted frame state ambient types live
            regions pending world source.compatible id ty roots typingAfter rootsAfter checked
          simp only [evaluated, Goose.Proofs.Exit.stepState, ExecutionStep.ok.injEq, true_and]
          intro result after ⟨sameValue, sameState⟩
          subst result after
          exact valid
  exact ⟨result.1, result.2, by simpa only [result.1] using world, by simpa only [result.1] using source⟩

#print axioms evalValue_checked_scalar_complete

end Goose.Proofs.ConstructionAcceptedExecution

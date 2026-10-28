import Goose.Proofs.ConstructionAcceptedEarlierCallerObservations
import Goose.Proofs.ConstructionAcceptedNestedArithmeticComposition

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

def EarlierScalarOutcome (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (ty : Ty) (outcome : ExecutionStep Value) : Prop :=
  ∃ nextTypes nextLive nextAmbient,
    RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
    before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
    AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
    AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
    FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
    EarlierCallerObservations before.nextAct before (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
    (match outcome with
     | .ok value _ => nextAmbient = ambient ∧ ValueRepresentation ty value
     | .stop .. => True | .escape .. | .jump .. => False)

theorem evalValue_binary_earlier_compose (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (integer : Goose.Core.IntTy)
    (operation : Goose.Core.BinOp) (left right : Expr) (origin : Nat)
    (leftSafe : EarlierScalarOutcome config accepted frame before ambient types regions pending (.int integer)
      (evalValue fuel config frame.interpretation.environment left before))
    (rightSafe : ∀ state currentTypes currentLive,
      AcceptedWorld config frame.initialized state ambient currentTypes currentLive regions pending →
      AcceptedFrame config accepted frame state currentTypes →
      EarlierScalarOutcome config accepted frame state ambient currentTypes regions pending (.int integer)
        (evalValue fuel config frame.interpretation.environment right state)) :
    EarlierScalarOutcome config accepted frame before ambient types regions pending (.int integer)
      (evalValue (fuel + 1) config frame.interpretation.environment (.bin operation left right origin) before) := by
  obtain ⟨middleTypes, middleLive, middleAmbient, extend, acts, scopes, world, source, clear, observed, result⟩ := leftSafe
  cases leftRun : evalValue fuel config frame.interpretation.environment left before with
  | stop reason after =>
    simp only [leftRun, Goose.Proofs.Exit.stepState] at acts scopes world source clear observed result
    simp only [EarlierScalarOutcome, evalValue, leftRun, bind, Goose.Proofs.Exit.stepState]
    exact ⟨middleTypes, middleLive, middleAmbient, extend, acts, scopes, world, source, clear, observed, trivial⟩
  | escape target carriers after | jump target kind after => simp [leftRun] at result
  | ok first middle =>
    simp only [leftRun, Goose.Proofs.Exit.stepState] at acts scopes world source clear observed result
    obtain ⟨rfl, represented⟩ := result
    cases represented with
    | stored _ _ nonfixed _ => cases nonfixed
    | integer _ first =>
      obtain ⟨finalTypes, finalLive, finalAmbient, extend2, acts2, scopes2, finalWorld, finalSource, finalClear, observed2, result2⟩ :=
        rightSafe middle middleTypes middleLive world source
      cases rightRun : evalValue fuel config frame.interpretation.environment right middle with
      | stop reason after =>
        simp only [rightRun, Goose.Proofs.Exit.stepState] at acts2 scopes2 finalWorld finalSource finalClear observed2 result2
        simp only [EarlierScalarOutcome, evalValue, leftRun, rightRun, bind, expectInt, pure, Goose.Proofs.Exit.stepState]
        exact ⟨finalTypes, finalLive, finalAmbient, (fun root ty found => extend2 root ty (extend root ty found)),
          Nat.le_trans acts acts2, Nat.le_trans scopes scopes2, finalWorld, finalSource, finalClear, observed.trans acts observed2, trivial⟩
      | escape target carriers after | jump target kind after => simp [rightRun] at result2
      | ok second after =>
        simp only [rightRun, Goose.Proofs.Exit.stepState] at acts2 scopes2 finalWorld finalSource finalClear observed2 result2
        obtain ⟨ambientEq, represented⟩ := result2
        cases represented with
        | stored _ _ nonfixed _ => cases nonfixed
        | integer _ second =>
          cases computed : Goose.Core.evalBin config.profile operation integer first second with
          | error reason =>
            simp only [EarlierScalarOutcome, evalValue, leftRun, rightRun, bind, expectInt, pure, sameIntType,
              beq_self_eq_true, ↓reduceIte, computed, abortAt, EvalM.stop, Goose.Proofs.Exit.stepState]
            exact ⟨finalTypes, finalLive, finalAmbient, (fun root ty found => extend2 root ty (extend root ty found)),
              Nat.le_trans acts acts2, Nat.le_trans scopes scopes2, finalWorld, finalSource, finalClear, observed.trans acts observed2, trivial⟩
          | ok value =>
            simp only [EarlierScalarOutcome, evalValue, leftRun, rightRun, bind, expectInt, pure, sameIntType,
              beq_self_eq_true, ↓reduceIte, computed, Goose.Proofs.Exit.stepState]
            exact ⟨finalTypes, finalLive, finalAmbient, (fun root ty found => extend2 root ty (extend root ty found)),
              Nat.le_trans acts acts2, Nat.le_trans scopes scopes2, finalWorld, finalSource, finalClear, observed.trans acts observed2,
              ambientEq, .integer integer value⟩

#print axioms evalValue_binary_earlier_compose
end Goose.Proofs.ConstructionAcceptedExecution

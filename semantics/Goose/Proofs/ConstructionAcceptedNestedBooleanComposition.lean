import Goose.Proofs.ConstructionAcceptedNestedArithmeticComposition
import Goose.Proofs.ConstructionAcceptedBinaryComplete

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem nestedShortCircuit_operands (conjunction : Bool) (frame : ConstructionSourceFrame) (fuel : Nat)
    (left right : Expr) (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (fuelAt : frame.typingFuel = fuel + 1)
    (checked : CheckedValue frame (scalarShortCircuit conjunction left right) ty roots typingAfter rootsAfter) :
    ∃ middle leftRoots rightRoots rootMiddle,
      ty = .bool ∧ roots = [] ∧
      CheckedValue (ordinaryOperandFrame frame fuel) left .bool leftRoots middle rootMiddle ∧
      CheckedValue { ordinaryOperandFrame frame fuel with typingCounter := middle, rootCursor := rootMiddle }
        right .bool rightRoots typingAfter rootsAfter := by
  have typing := checked.typing
  rw [fuelAt] at typing
  obtain ⟨middle, sameTy, leftTyping, rightTyping⟩ :=
    typeExpr_shortCircuit_operands conjunction fuel frame.typing left right frame.typingCounter typingAfter ty typing
  have provenance : rpExpr frame.source (.cmp .eq left right) frame.rootCursor = .ok (roots, rootsAfter) := by
    cases conjunction <;> exact checked.provenance
  obtain ⟨sameRoots, leftRoots, rightRoots, rootMiddle, leftRooted, rightRooted, included⟩ :=
    rpExpr_cmp_operands frame.source .eq left right frame.rootCursor rootsAfter roots provenance
  have available : GlobalEffectsAvailable frame.interpretation frame.initialized rootMiddle.eff := by
    intro target member global rooted
    exact checked.available target (included member) global rooted
  exact ⟨middle, leftRoots, rightRoots, rootMiddle, sameTy, sameRoots,
    ⟨leftTyping, leftRooted, available⟩, ⟨rightTyping, rightRooted, checked.available⟩⟩


theorem nestedValueShortCircuit_compose (conjunction : Bool) (fuel : Nat) (config : EvalConfig)
    (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (left right : Expr) (before : ExecutionState)
    (leftSafe : NestedValueOutcome config accepted frame ambient types live .bool
      (evalValue fuel config frame.interpretation.environment left before))
    (rightSafe : ∀ state, AcceptedWorld config frame.initialized state ambient types live [] [] →
      AcceptedFrame config accepted frame state types →
      NestedValueOutcome config accepted frame ambient types live .bool
        (evalValue fuel config frame.interpretation.environment right state)) :
    NestedValueOutcome config accepted frame ambient types live .bool
      (evalValue (fuel + 1) config frame.interpretation.environment (scalarShortCircuit conjunction left right) before) := by
  cases leftRun : evalValue fuel config frame.interpretation.environment left before with
  | stop reason after =>
    simp only [NestedValueOutcome, leftRun, Goose.Proofs.Exit.stepState] at leftSafe
    cases conjunction <;> simpa [scalarShortCircuit, NestedValueOutcome, evalValue, leftRun, bind, Goose.Proofs.Exit.stepState] using leftSafe
  | escape address carriers after | jump target kind after =>
    simp only [NestedValueOutcome, leftRun] at leftSafe
    exact leftSafe.2.2.elim
  | ok value middle =>
    simp only [NestedValueOutcome, leftRun, Goose.Proofs.Exit.stepState] at leftSafe
    cases represented : leftSafe.2.2.1 with
    | stored => contradiction
    | boolean first =>
      cases conjunction <;> cases first <;>
        simp only [scalarShortCircuit, Bool.false_eq_true, ↓reduceIte, NestedValueOutcome, evalValue, leftRun,
          bind, expectBool, pure, Goose.Proofs.Exit.stepState]
      all_goals first
        | exact ⟨leftSafe.1, leftSafe.2.1, .boolean _, .boolean _⟩
        | skip
      all_goals
        have rightResult := rightSafe middle leftSafe.1 leftSafe.2.1
        cases rightRun : evalValue fuel config frame.interpretation.environment right middle with
        | stop reason after =>
          simp only [NestedValueOutcome, rightRun, Goose.Proofs.Exit.stepState] at rightResult
          simpa [rightRun, bind, Goose.Proofs.Exit.stepState] using rightResult
        | escape address carriers after | jump target kind after =>
          simp only [NestedValueOutcome, rightRun] at rightResult
          exact rightResult.2.2.elim
        | ok value after =>
          simp only [NestedValueOutcome, rightRun, Goose.Proofs.Exit.stepState] at rightResult
          cases represented : rightResult.2.2.1 with
          | stored => contradiction
          | boolean second =>
            simpa [rightRun, bind, expectBool, pure, Goose.Proofs.Exit.stepState] using rightResult

#print axioms nestedValueShortCircuit_compose
#print axioms nestedShortCircuit_operands
end Goose.Proofs.ConstructionAcceptedExecution

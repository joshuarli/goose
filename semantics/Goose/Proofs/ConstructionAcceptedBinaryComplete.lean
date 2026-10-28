import Goose.Proofs.ConstructionAcceptedBinaryCursor

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem evalValue_checked_binary_complete (operation : Goose.Core.BinOp) (left right : Expr)
    (origin : Goose.Core.OriginId) (leftForm : AcceptedNumericExpression left) (rightForm : AcceptedNumericExpression right)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState) (checked : CheckedValue frame (.bin operation left right origin) ty roots typingAfter rootsAfter) :
    let outcome := evalValue fuel config frame.interpretation.environment (.bin operation left right origin) state
    Goose.Proofs.Exit.stepState outcome = state ∧
      (∀ value after, outcome = .ok value after → AcceptedValue config.layout types frame.interpretation after ty roots value) ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types := by
  cases depth : frame.typingFuel with
  | zero => have typing := checked.typing; rw [depth] at typing; change Except.error _ = Except.ok _ at typing; cases typing
  | succ n =>
    obtain ⟨integer, middle, leftRoots, rightRoots, rootMiddle, rootFinal, sameTy, sameRoots, leftChecked, rightChecked⟩ :=
      checkedValue_bin_operands frame n operation left right origin ty roots typingAfter rootsAfter depth checked
    subst ty roots
    let leftFrame := ordinaryOperandFrame frame n
    let rightFrame := { ordinaryOperandFrame frame n with typingCounter := middle, rootCursor := rootMiddle }
    have leftSource := ordinaryOperandFrame_accepted accepted frame n state types source
    have rightSource := numericOperand_rightFrame_accepted accepted frame n state types source leftForm (.int integer)
      leftRoots middle rootMiddle leftChecked
    cases fuel with
    | zero => simp [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      have leftResult := evalValue_checked_numeric_complete leftForm fuel config accepted leftFrame state ambient types live regions pending
        world leftSource (.int integer) leftRoots middle rootMiddle leftChecked
      change Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment left state) = state ∧
        (∀ value after, evalValue fuel config frame.interpretation.environment left state = .ok value after →
          AcceptedValue config.layout types frame.interpretation after (.int integer) leftRoots value) ∧ _ at leftResult
      cases evaluatedLeft : evalValue fuel config frame.interpretation.environment left state with
      | stop reason after | escape reason carriers after | jump reason kind after =>
        simp only [evaluatedLeft, Goose.Proofs.Exit.stepState] at leftResult
        have same := leftResult.1
        subst after
        simp only [evalValue, evaluatedLeft, bind, Goose.Proofs.Exit.stepState, reduceCtorEq, true_and]
        exact ⟨fun _ _ impossible => False.elim impossible, world, source⟩
      | ok value after =>
        have acceptedLeft := leftResult.2.1 value after evaluatedLeft
        simp only [evaluatedLeft, Goose.Proofs.Exit.stepState] at leftResult
        have same := leftResult.1
        subst after
        cases represented : acceptedLeft.represented with
        | stored => contradiction
        | integer _ first =>
          have rightResult := evalValue_checked_numeric_complete rightForm fuel config accepted rightFrame state ambient types live regions pending
            world rightSource (.int integer) rightRoots typingAfter rootFinal rightChecked
          change Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment right state) = state ∧
            (∀ value after, evalValue fuel config frame.interpretation.environment right state = .ok value after →
              AcceptedValue config.layout types frame.interpretation after (.int integer) rightRoots value) ∧ _ at rightResult
          cases evaluatedRight : evalValue fuel config frame.interpretation.environment right state with
          | stop reason after | escape reason carriers after | jump reason kind after =>
            simp only [evaluatedRight, Goose.Proofs.Exit.stepState] at rightResult
            have same := rightResult.1
            subst after
            simp only [evalValue, evaluatedLeft, evaluatedRight, bind, expectInt, pure, Goose.Proofs.Exit.stepState,
              reduceCtorEq, true_and]
            exact ⟨fun _ _ impossible => False.elim impossible, world, source⟩
          | ok value after =>
            have acceptedRight := rightResult.2.1 value after evaluatedRight
            simp only [evaluatedRight, Goose.Proofs.Exit.stepState] at rightResult
            have same := rightResult.1
            subst after
            cases represented : acceptedRight.represented with
            | stored => contradiction
            | integer _ second =>
              cases computed : Goose.Core.evalBin config.profile operation integer first second with
              | error reason =>
                simp only [evalValue, evaluatedLeft, evaluatedRight, bind, expectInt, pure, sameIntType,
                  beq_self_eq_true, ↓reduceIte, computed, abortAt, EvalM.stop, Goose.Proofs.Exit.stepState,
                  reduceCtorEq, true_and]
                exact ⟨fun _ _ impossible => False.elim impossible, world, source⟩
              | ok number =>
                simp only [evalValue, evaluatedLeft, evaluatedRight, bind, expectInt, pure, sameIntType,
                  beq_self_eq_true, ↓reduceIte, computed, Goose.Proofs.Exit.stepState, ExecutionStep.ok.injEq, true_and]
                refine ⟨?_, world, source⟩
                intro output after same
                obtain ⟨rfl, rfl⟩ := same
                exact acceptedValue_integer config.layout types frame.interpretation state integer number

theorem evalValue_checked_comparison_complete (operation : Goose.Core.CmpOp) (left right : Expr)
    (leftForm : AcceptedNumericExpression left) (rightForm : AcceptedNumericExpression right)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState) (checked : CheckedValue frame (.cmp operation left right) ty roots typingAfter rootsAfter) :
    let outcome := evalValue fuel config frame.interpretation.environment (.cmp operation left right) state
    Goose.Proofs.Exit.stepState outcome = state ∧
      (∀ value after, outcome = .ok value after → AcceptedValue config.layout types frame.interpretation after ty roots value) ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types := by
  cases depth : frame.typingFuel with
  | zero => have typing := checked.typing; rw [depth] at typing; change Except.error _ = Except.ok _ at typing; cases typing
  | succ n =>
    obtain ⟨operandTy, middle, leftRoots, rightRoots, rootMiddle, sameTy, sameRoots, operandKind, leftChecked, rightChecked⟩ :=
      checkedValue_cmp_operands frame n operation left right ty roots typingAfter rootsAfter depth checked
    subst ty roots
    let leftFrame := ordinaryOperandFrame frame n
    let rightFrame := { ordinaryOperandFrame frame n with typingCounter := middle, rootCursor := rootMiddle }
    have leftSource := ordinaryOperandFrame_accepted accepted frame n state types source
    have rightSource := numericOperand_rightFrame_accepted accepted frame n state types source leftForm operandTy
      leftRoots middle rootMiddle leftChecked
    cases fuel with
    | zero => simp [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      have leftResult := evalValue_checked_numeric_complete leftForm fuel config accepted leftFrame state ambient types live regions pending
        world leftSource operandTy leftRoots middle rootMiddle leftChecked
      change Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment left state) = state ∧
        (∀ value after, evalValue fuel config frame.interpretation.environment left state = .ok value after →
          AcceptedValue config.layout types frame.interpretation after operandTy leftRoots value) ∧ _ at leftResult
      cases evaluatedLeft : evalValue fuel config frame.interpretation.environment left state with
      | stop reason after | escape reason carriers after | jump reason kind after =>
        simp only [evaluatedLeft, Goose.Proofs.Exit.stepState] at leftResult
        have same := leftResult.1
        subst after
        simp only [evalValue, evaluatedLeft, bind, Goose.Proofs.Exit.stepState, reduceCtorEq, true_and]
        exact ⟨fun _ _ impossible => False.elim impossible, world, source⟩
      | ok first after =>
        have acceptedLeft := leftResult.2.1 first after evaluatedLeft
        simp only [evaluatedLeft, Goose.Proofs.Exit.stepState] at leftResult
        have same := leftResult.1
        subst after
        have rightResult := evalValue_checked_numeric_complete rightForm fuel config accepted rightFrame state ambient types live regions pending
          world rightSource operandTy rightRoots typingAfter rootsAfter rightChecked
        change Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment right state) = state ∧
          (∀ value after, evalValue fuel config frame.interpretation.environment right state = .ok value after →
            AcceptedValue config.layout types frame.interpretation after operandTy rightRoots value) ∧ _ at rightResult
        cases evaluatedRight : evalValue fuel config frame.interpretation.environment right state with
        | stop reason after | escape reason carriers after | jump reason kind after =>
          simp only [evaluatedRight, Goose.Proofs.Exit.stepState] at rightResult
          have same := rightResult.1
          subst after
          simp only [evalValue, evaluatedLeft, evaluatedRight, bind, Goose.Proofs.Exit.stepState, reduceCtorEq, true_and]
          exact ⟨fun _ _ impossible => False.elim impossible, world, source⟩
        | ok second after =>
          have acceptedRight := rightResult.2.1 second after evaluatedRight
          simp only [evaluatedRight, Goose.Proofs.Exit.stepState] at rightResult
          have same := rightResult.1
          subst after
          rcases operandKind with boolean | ⟨integer, integerType⟩
          · subst operandTy
            cases leftRep : acceptedLeft.represented with
            | stored => contradiction
            | boolean first =>
              cases rightRep : acceptedRight.represented with
              | stored => contradiction
              | boolean second =>
                simp only [evalValue, evaluatedLeft, evaluatedRight, bind, comparable, pure,
                  Goose.Proofs.Exit.stepState, ExecutionStep.ok.injEq, true_and]
                refine ⟨?_, world, source⟩
                intro value after same
                obtain ⟨rfl, rfl⟩ := same
                exact acceptedValue_boolean config.layout types frame.interpretation state _
          · subst operandTy
            cases leftRep : acceptedLeft.represented with
            | stored => contradiction
            | integer _ first =>
              cases rightRep : acceptedRight.represented with
              | stored => contradiction
              | integer _ second =>
                simp only [evalValue, evaluatedLeft, evaluatedRight, bind, comparable, sameIntType, beq_self_eq_true,
                  ↓reduceIte, pure, Goose.Proofs.Exit.stepState, ExecutionStep.ok.injEq, true_and]
                refine ⟨?_, world, source⟩
                intro value after same
                obtain ⟨rfl, rfl⟩ := same
                exact acceptedValue_boolean config.layout types frame.interpretation state _

#print axioms evalValue_checked_comparison_complete
#print axioms evalValue_checked_binary_complete
end Goose.Proofs.ConstructionAcceptedExecution

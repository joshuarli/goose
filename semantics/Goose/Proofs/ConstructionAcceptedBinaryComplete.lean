import Goose.Proofs.ConstructionAcceptedBinaryCursor

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

private def CheckedCursor (expression : Expr) : Prop :=
  ∀ (frame : ConstructionSourceFrame) (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState),
    CheckedValue frame expression ty roots typingAfter rootsAfter →
      typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar

private theorem rightFrame_accepted {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (fuel : Nat) (state : ExecutionState) (types : RootTypes)
    (valid : AcceptedFrame config accepted frame state types) {expression : Expr}
    (cursorProperty : CheckedCursor expression) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue (ordinaryOperandFrame frame fuel) expression ty roots typingAfter rootsAfter) :
    AcceptedFrame config accepted
      { ordinaryOperandFrame frame fuel with typingCounter := typingAfter, rootCursor := rootsAfter } state types := by
  obtain ⟨counter, cursor⟩ := cursorProperty (ordinaryOperandFrame frame fuel) ty roots typingAfter rootsAfter checked
  have initial := ordinaryOperandFrame_accepted accepted frame fuel state types valid
  refine ⟨⟨initial.compatible.module, initial.compatible.rootModule, initial.compatible.variables,
    initial.compatible.sourceVariables, initial.compatible.scopes, initial.compatible.globalCount,
    initial.compatible.globals, initial.compatible.initialized, ?_, ?_, ?_, initial.compatible.initializing,
    initial.compatible.currentScope, initial.compatible.origin⟩,
    initial.frontier, initial.scopeFrontier, ?_, initial.aliases, initial.locals, initial.localTypes, ?_, ?_,
    initial.futureGlobals, initial.direct, initial.contents⟩
  · simpa only [counter, cursor] using initial.compatible.declarations
  · simpa only [counter] using initial.compatible.typingBound
  · simpa only [cursor] using initial.compatible.visible
  · simpa only [cursor] using initial.initializingBefore
  · simpa only [cursor] using initial.uninitializedLocals
  · simpa only [cursor] using initial.uninitializedTypes

private theorem binary_complete (operation : Goose.Core.BinOp) (left right : Expr)
    (origin : Goose.Core.OriginId) (leftCursor : CheckedCursor left) (leftComplete : CheckedExpressionEvaluation left) (rightComplete : CheckedExpressionEvaluation right)
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
    have rightSource := rightFrame_accepted accepted frame n state types source leftCursor (.int integer)
      leftRoots middle rootMiddle leftChecked
    cases fuel with
    | zero => simp [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      have leftResult := leftComplete fuel config accepted leftFrame state ambient types live regions pending
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
          have rightResult := rightComplete fuel config accepted rightFrame state ambient types live regions pending
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

private theorem comparison_complete (operation : Goose.Core.CmpOp) (left right : Expr)
    (leftCursor : CheckedCursor left) (leftComplete : CheckedExpressionEvaluation left) (rightComplete : CheckedExpressionEvaluation right)
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
    have rightSource := rightFrame_accepted accepted frame n state types source leftCursor operandTy
      leftRoots middle rootMiddle leftChecked
    cases fuel with
    | zero => simp [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      have leftResult := leftComplete fuel config accepted leftFrame state ambient types live regions pending
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
        have rightResult := rightComplete fuel config accepted rightFrame state ambient types live regions pending
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


theorem shortCircuit_operands (conjunction : Bool) (frame : ConstructionSourceFrame) (fuel : Nat)
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

private theorem shortCircuit_complete (conjunction : Bool) (left right : Expr)
    (leftCursor : CheckedCursor left) (leftComplete : CheckedExpressionEvaluation left)
    (rightComplete : CheckedExpressionEvaluation right) : CheckedExpressionEvaluation (scalarShortCircuit conjunction left right) := by
  intro fuel config accepted frame state ambient types live regions pending world source ty roots typingAfter rootsAfter checked
  cases depth : frame.typingFuel with
  | zero => have typing := checked.typing; rw [depth] at typing; change Except.error _ = Except.ok _ at typing; cases typing
  | succ n =>
    obtain ⟨middle, leftRoots, rightRoots, rootMiddle, sameTy, sameRoots, leftChecked, rightChecked⟩ :=
      shortCircuit_operands conjunction frame n left right ty roots typingAfter rootsAfter depth checked
    subst ty roots
    let leftFrame := ordinaryOperandFrame frame n
    let rightFrame := { ordinaryOperandFrame frame n with typingCounter := middle, rootCursor := rootMiddle }
    have leftSource := ordinaryOperandFrame_accepted accepted frame n state types source
    have rightSource := rightFrame_accepted accepted frame n state types source leftCursor .bool leftRoots middle rootMiddle leftChecked
    cases fuel with
    | zero => cases conjunction <;> simp [scalarShortCircuit, evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      have leftResult := leftComplete fuel config accepted leftFrame state ambient types live regions pending
        world leftSource .bool leftRoots middle rootMiddle leftChecked
      change Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment left state) = state ∧
        (∀ value after, evalValue fuel config frame.interpretation.environment left state = .ok value after →
          AcceptedValue config.layout types frame.interpretation after .bool leftRoots value) ∧ _ at leftResult
      cases evaluatedLeft : evalValue fuel config frame.interpretation.environment left state with
      | stop reason after | escape reason carriers after | jump reason kind after =>
        simp only [evaluatedLeft, Goose.Proofs.Exit.stepState] at leftResult
        have same := leftResult.1
        subst after
        cases conjunction <;> simp only [scalarShortCircuit, Bool.false_eq_true, ↓reduceIte, evalValue, evaluatedLeft, bind,
          Goose.Proofs.Exit.stepState, reduceCtorEq, true_and] <;>
          exact ⟨fun _ _ impossible => False.elim impossible, world, source⟩
      | ok value after =>
        have acceptedLeft := leftResult.2.1 value after evaluatedLeft
        simp only [evaluatedLeft, Goose.Proofs.Exit.stepState] at leftResult
        have same := leftResult.1
        subst after
        cases represented : acceptedLeft.represented with
        | stored => contradiction
        | boolean first =>
          cases conjunction <;> cases first <;>
            simp only [scalarShortCircuit, Bool.false_eq_true, ↓reduceIte, evalValue, evaluatedLeft, bind, expectBool, pure,
              Goose.Proofs.Exit.stepState, ExecutionStep.ok.injEq, true_and]
          all_goals first
            | refine ⟨?_, world, source⟩
              intro output after same
              obtain ⟨rfl, rfl⟩ := same
              exact acceptedValue_boolean config.layout types frame.interpretation state _
            | skip
          all_goals
            have rightResult := rightComplete fuel config accepted rightFrame state ambient types live regions pending
              world rightSource .bool rightRoots typingAfter rootsAfter rightChecked
            change Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment right state) = state ∧
              (∀ value after, evalValue fuel config frame.interpretation.environment right state = .ok value after →
                AcceptedValue config.layout types frame.interpretation after .bool rightRoots value) ∧ _ at rightResult
            cases evaluatedRight : evalValue fuel config frame.interpretation.environment right state with
            | stop reason after | escape reason carriers after | jump reason kind after =>
              simp only [evaluatedRight, Goose.Proofs.Exit.stepState] at rightResult
              have same := rightResult.1
              subst after
              simp only [reduceCtorEq, true_and]
              exact ⟨fun _ _ impossible => False.elim impossible, world, source⟩
            | ok value after =>
              have acceptedRight := rightResult.2.1 value after evaluatedRight
              simp only [evaluatedRight, Goose.Proofs.Exit.stepState] at rightResult
              have same := rightResult.1
              subst after
              cases represented : acceptedRight.represented with
              | stored => contradiction
              | boolean second =>
                simp only [ExecutionStep.ok.injEq, true_and]
                refine ⟨?_, world, source⟩
                intro output after same
                obtain ⟨rfl, rfl⟩ := same
                exact acceptedValue_boolean config.layout types frame.interpretation state second

inductive AcceptedBinaryExpression : Expr → Prop
  | numeric {expression : Expr} : AcceptedNumericExpression expression → AcceptedBinaryExpression expression
  | binary {left right : Expr} (operation : Goose.Core.BinOp) (origin : Goose.Core.OriginId) :
      AcceptedBinaryExpression left → AcceptedBinaryExpression right → AcceptedBinaryExpression (.bin operation left right origin)
  | comparison {left right : Expr} (operation : Goose.Core.CmpOp) :
      AcceptedBinaryExpression left → AcceptedBinaryExpression right → AcceptedBinaryExpression (.cmp operation left right)
  | conjunction {left right : Expr} : AcceptedBinaryExpression left → AcceptedBinaryExpression right →
      AcceptedBinaryExpression (.and left right)
  | disjunction {left right : Expr} : AcceptedBinaryExpression left → AcceptedBinaryExpression right →
      AcceptedBinaryExpression (.or left right)
  | not {expression : Expr} : AcceptedBinaryExpression expression → AcceptedBinaryExpression (.not expression)
  | unary {expression : Expr} (operation : Goose.Core.UnOp) (origin : Goose.Core.OriginId) :
      AcceptedBinaryExpression expression → AcceptedBinaryExpression (.un operation expression origin)
  | conversion {expression : Expr} (kind : Goose.Core.ConvKind) (target : Ty) (origin : Goose.Core.OriginId) :
      AcceptedBinaryExpression expression → AcceptedBinaryExpression (.conv kind target expression origin)

private theorem bin_final_nextVar (frame : ConstructionSourceFrame) (operation : Goose.Core.BinOp) (left right : Expr)
    (origin : Goose.Core.OriginId) (roots leftRoots rightRoots : List RootRef) (after middle final : RState)
    (checked : rpExpr frame.source (.bin operation left right origin) frame.rootCursor = .ok (roots, after))
    (first : rpExpr frame.source left frame.rootCursor = .ok (leftRoots, middle))
    (second : rpExpr frame.source right middle = .ok (rightRoots, final)) : after.nextVar = final.nextVar := by
  change (Except.bind (rpExpr frame.source left frame.rootCursor) _) = .ok (roots, after) at checked
  simp only [first, Except.bind] at checked
  change (Except.bind (rpExpr frame.source right middle) _) = .ok (roots, after) at checked
  simp only [second, Except.bind] at checked
  cases operation <;> first
    | change Except.ok ([], final) = Except.ok (roots, after) at checked; cases checked; rfl
    | change Except.ok ([], { final with eff := { final.eff with aborts := true } }) = Except.ok (roots, after) at checked
      cases checked; rfl

private theorem binary_recursive {expression : Expr} (form : AcceptedBinaryExpression expression) :
    CheckedCursor expression ∧ CheckedExpressionEvaluation expression := by
  induction form with
  | numeric form =>
    refine ⟨?_, ?_⟩
    · intro frame ty roots typingAfter rootsAfter checked
      exact numeric_checked_cursor form frame ty roots typingAfter rootsAfter checked
    · intro fuel config accepted frame state ambient types live regions pending world source ty roots typingAfter rootsAfter checked
      exact evalValue_checked_numeric_complete form fuel config accepted frame state ambient types live regions pending world source
        ty roots typingAfter rootsAfter checked
  | @binary left right operation origin leftForm rightForm leftIH rightIH =>
    refine ⟨?_, binary_complete operation left right origin leftIH.1 leftIH.2 rightIH.2⟩
    intro frame ty roots typingAfter rootsAfter checked
    cases depth : frame.typingFuel with
    | zero => have typing := checked.typing; rw [depth] at typing; change Except.error _ = Except.ok _ at typing; cases typing
    | succ fuel =>
      obtain ⟨integer, middle, leftRoots, rightRoots, rootMiddle, rootFinal, _, _, leftChecked, rightChecked⟩ :=
        checkedValue_bin_operands frame fuel operation left right origin ty roots typingAfter rootsAfter depth checked
      have leftCursor := leftIH.1 (ordinaryOperandFrame frame fuel) (.int integer) leftRoots middle rootMiddle leftChecked
      have rightCursor := rightIH.1 { ordinaryOperandFrame frame fuel with typingCounter := middle, rootCursor := rootMiddle }
        (.int integer) rightRoots typingAfter rootFinal rightChecked
      have finalCursor := bin_final_nextVar frame operation left right origin roots leftRoots rightRoots rootsAfter rootMiddle rootFinal
        checked.provenance leftChecked.provenance rightChecked.provenance
      exact ⟨rightCursor.1.trans leftCursor.1, finalCursor.trans (rightCursor.2.trans leftCursor.2)⟩
  | @comparison left right operation leftForm rightForm leftIH rightIH =>
    refine ⟨?_, comparison_complete operation left right leftIH.1 leftIH.2 rightIH.2⟩
    intro frame ty roots typingAfter rootsAfter checked
    cases depth : frame.typingFuel with
    | zero => have typing := checked.typing; rw [depth] at typing; change Except.error _ = Except.ok _ at typing; cases typing
    | succ fuel =>
      obtain ⟨operandTy, middle, leftRoots, rightRoots, rootMiddle, _, _, _, leftChecked, rightChecked⟩ :=
        checkedValue_cmp_operands frame fuel operation left right ty roots typingAfter rootsAfter depth checked
      have leftCursor := leftIH.1 (ordinaryOperandFrame frame fuel) operandTy leftRoots middle rootMiddle leftChecked
      have rightCursor := rightIH.1 { ordinaryOperandFrame frame fuel with typingCounter := middle, rootCursor := rootMiddle }
        operandTy rightRoots typingAfter rootsAfter rightChecked
      exact ⟨rightCursor.1.trans leftCursor.1, rightCursor.2.trans leftCursor.2⟩

  | @conjunction left right leftForm rightForm leftIH rightIH =>
    refine ⟨?_, shortCircuit_complete true left right leftIH.1 leftIH.2 rightIH.2⟩
    intro frame ty roots typingAfter rootsAfter checked
    cases depth : frame.typingFuel with
    | zero => have typing := checked.typing; rw [depth] at typing; change Except.error _ = Except.ok _ at typing; cases typing
    | succ fuel =>
      obtain ⟨middle, leftRoots, rightRoots, rootMiddle, _, _, leftChecked, rightChecked⟩ :=
        shortCircuit_operands true frame fuel left right ty roots typingAfter rootsAfter depth checked
      have leftCursor := leftIH.1 (ordinaryOperandFrame frame fuel) .bool leftRoots middle rootMiddle leftChecked
      have rightCursor := rightIH.1 { ordinaryOperandFrame frame fuel with typingCounter := middle, rootCursor := rootMiddle }
        .bool rightRoots typingAfter rootsAfter rightChecked
      exact ⟨rightCursor.1.trans leftCursor.1, rightCursor.2.trans leftCursor.2⟩
  | @disjunction left right leftForm rightForm leftIH rightIH =>
    refine ⟨?_, shortCircuit_complete false left right leftIH.1 leftIH.2 rightIH.2⟩
    intro frame ty roots typingAfter rootsAfter checked
    cases depth : frame.typingFuel with
    | zero => have typing := checked.typing; rw [depth] at typing; change Except.error _ = Except.ok _ at typing; cases typing
    | succ fuel =>
      obtain ⟨middle, leftRoots, rightRoots, rootMiddle, _, _, leftChecked, rightChecked⟩ :=
        shortCircuit_operands false frame fuel left right ty roots typingAfter rootsAfter depth checked
      have leftCursor := leftIH.1 (ordinaryOperandFrame frame fuel) .bool leftRoots middle rootMiddle leftChecked
      have rightCursor := rightIH.1 { ordinaryOperandFrame frame fuel with typingCounter := middle, rootCursor := rootMiddle }
        .bool rightRoots typingAfter rootsAfter rightChecked
      exact ⟨rightCursor.1.trans leftCursor.1, rightCursor.2.trans leftCursor.2⟩
  | @not expression operand ih =>
    refine ⟨?_, checkedExpressionEvaluation_not expression ih.2⟩
    intro frame ty roots typingAfter rootsAfter checked
    cases depth : frame.typingFuel with
    | zero => have typing := checked.typing; rw [depth] at typing; change Except.error _ = Except.ok _ at typing; cases typing
    | succ fuel =>
      obtain ⟨_, _, operandRoots, operandChecked⟩ := checkedValue_not_operand frame fuel expression ty roots typingAfter rootsAfter depth checked
      exact ih.1 (ordinaryOperandFrame frame fuel) .bool operandRoots typingAfter rootsAfter operandChecked
  | @unary expression operation origin operand ih =>
    refine ⟨?_, checkedExpressionEvaluation_unary expression operation origin ih.2⟩
    intro frame ty roots typingAfter rootsAfter checked
    cases depth : frame.typingFuel with
    | zero => have typing := checked.typing; rw [depth] at typing; change Except.error _ = Except.ok _ at typing; cases typing
    | succ fuel =>
      obtain ⟨integer, operandRoots, operandAfter, _, _, operandChecked⟩ :=
        checkedValue_un_operand frame fuel operation expression origin ty roots typingAfter rootsAfter depth checked
      obtain ⟨otherRoots, otherAfter, rooted, nextVar⟩ := rpExpr_un_nextVar frame.source operation expression origin
        frame.rootCursor rootsAfter roots checked.provenance
      have same := operandChecked.provenance.symm.trans rooted
      cases same
      have result := ih.1 (ordinaryOperandFrame frame fuel) (.int integer) operandRoots typingAfter operandAfter operandChecked
      exact ⟨result.1, nextVar.trans result.2⟩
  | @conversion expression kind target origin operand ih =>
    refine ⟨?_, checkedExpressionEvaluation_conversion expression kind target origin ih.2⟩
    intro frame ty roots typingAfter rootsAfter checked
    cases depth : frame.typingFuel with
    | zero => have typing := checked.typing; rw [depth] at typing; change Except.error _ = Except.ok _ at typing; cases typing
    | succ fuel =>
      obtain ⟨integer, _, operandRoots, operandAfter, _, _, _, operandChecked⟩ :=
        checkedValue_conv_operand frame fuel kind target expression origin ty roots typingAfter rootsAfter depth checked
      obtain ⟨otherRoots, otherAfter, rooted, nextVar⟩ := rpExpr_conv_nextVar frame.source kind target expression origin
        frame.rootCursor rootsAfter roots checked.provenance
      have same := operandChecked.provenance.symm.trans rooted
      cases same
      have result := ih.1 (ordinaryOperandFrame frame fuel) (.int integer) operandRoots typingAfter operandAfter operandChecked
      exact ⟨result.1, nextVar.trans result.2⟩

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
  exact binary_complete operation left right origin (numeric_checked_cursor leftForm)
    (evalValue_checked_numeric_complete leftForm) (evalValue_checked_numeric_complete rightForm)
    fuel config accepted frame state ambient types live regions pending world source ty roots typingAfter rootsAfter checked

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
  exact comparison_complete operation left right (numeric_checked_cursor leftForm)
    (evalValue_checked_numeric_complete leftForm) (evalValue_checked_numeric_complete rightForm)
    fuel config accepted frame state ambient types live regions pending world source ty roots typingAfter rootsAfter checked

theorem evalValue_checked_binary_recursive {expression : Expr} (form : AcceptedBinaryExpression expression)
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
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types :=
  (binary_recursive form).2 fuel config accepted frame state ambient types live regions pending world source ty roots typingAfter rootsAfter checked

theorem checked_binary_recursive_cursor {expression : Expr} (form : AcceptedBinaryExpression expression)
    (frame : ConstructionSourceFrame) (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame expression ty roots typingAfter rootsAfter) :
    typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar :=
  (binary_recursive form).1 frame ty roots typingAfter rootsAfter checked

#print axioms shortCircuit_operands
#print axioms shortCircuit_complete
#print axioms checked_binary_recursive_cursor
#print axioms evalValue_checked_binary_recursive
#print axioms evalValue_checked_comparison_complete
#print axioms evalValue_checked_binary_complete


end Goose.Proofs.ConstructionAcceptedExecution

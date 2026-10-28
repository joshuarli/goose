import Goose.Proofs.ConstructionAcceptedNestedBooleanComposition

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private theorem nestedComplete_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

def FlatGlobalsAreScalar (config : EvalConfig) : Prop :=
  ∀ (id : Nat) (descriptor : Global), config.module.globals[id]? = some descriptor → descriptor.ty.flat = true → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool

mutual
theorem nestedScalarExpression_complete {expression : Expr} (form : NestedScalarExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config frame.initialized before ambient types live [] [])
    (source : AcceptedFrame config accepted frame before types) (empty : frame.interpretation.environment.vars = #[])
    (globalLimit : frame.typing.globalLimit ≤ frame.initialized)
    (noParameters : ∀ parameter global, ¬ frame.interpretation.parameters parameter (.global global))
    (scalars : FlatGlobalsAreScalar config) (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame expression ty roots typingAfter rootsAfter) :
    NestedValueOutcome config accepted frame ambient types live ty (evalValue fuel config frame.interpretation.environment expression before) := by
  cases form with
  | scalar form => exact nestedValue_scalar fuel config accepted frame ambient types live ty _ form before world source roots typingAfter rootsAfter checked
  | @unary expression operation origin operand =>
    cases fuel with
    | zero => simp [NestedValueOutcome, evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      cases nesting : frame.typingFuel with
      | zero =>
        have typed := checked.typing
        rw [nesting] at typed
        change Except.error _ = Except.ok _ at typed
        cases typed
      | succ checkFuel =>
        obtain ⟨integer, operandRoots, operandAfter, sameTy, sameRoots, operandChecked⟩ :=
          checkedValue_un_operand frame checkFuel operation expression origin ty roots typingAfter rootsAfter nesting checked
        subst ty roots
        let operandFrame := ordinaryOperandFrame frame checkFuel
        have operandSource := ordinaryOperandFrame_accepted accepted frame checkFuel before types source
        have safe := nestedScalarExpression_complete operand fuel config accepted operandFrame before ambient types live world operandSource
          empty globalLimit noParameters scalars (.int integer) operandRoots typingAfter operandAfter operandChecked
        have safe' : NestedValueOutcome config accepted frame ambient types live (.int integer)
            (evalValue fuel config frame.interpretation.environment expression before) :=
          safe.retarget config accepted frame operandFrame ambient types live (.int integer) before _ source empty rfl rfl
        exact nestedValueUnary_compose fuel config accepted frame ambient types live integer operation expression origin before safe'
  | @binary left right operation origin leftForm rightForm =>
    cases fuel with
    | zero => simp [NestedValueOutcome, evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      cases nesting : frame.typingFuel with
      | zero =>
        have typed := checked.typing
        rw [nesting] at typed
        change Except.error _ = Except.ok _ at typed
        cases typed
      | succ checkFuel =>
        obtain ⟨integer, middle, leftRoots, rightRoots, rootMiddle, rootFinal, sameTy, sameRoots, leftChecked, rightChecked⟩ :=
          checkedValue_bin_operands frame checkFuel operation left right origin ty roots typingAfter rootsAfter nesting checked
        subst ty roots
        let leftFrame := ordinaryOperandFrame frame checkFuel
        let rightFrame := { leftFrame with
          typingCounter := middle
          rootCursor := rootMiddle }
        have leftFacts := nestedScalarExpression_cursors leftForm checkFuel leftFrame (.int integer) leftRoots middle rootMiddle rfl leftChecked
        have sameCounter : middle = frame.typingCounter := by simpa [leftFrame, ordinaryOperandFrame] using leftFacts.1
        have sameRoot : rootMiddle.nextVar = frame.rootCursor.nextVar := by simpa [leftFrame, ordinaryOperandFrame] using leftFacts.2
        have leftSource := ordinaryOperandFrame_accepted accepted frame checkFuel before types source
        have leftSafe := nestedScalarExpression_complete leftForm fuel config accepted leftFrame before ambient types live world leftSource
          empty globalLimit noParameters scalars (.int integer) leftRoots middle rootMiddle leftChecked
        have leftSafe' : NestedValueOutcome config accepted frame ambient types live (.int integer)
            (evalValue fuel config frame.interpretation.environment left before) :=
          leftSafe.retarget config accepted frame leftFrame ambient types live (.int integer) before _ source empty rfl rfl
        have rightSafe : ∀ state, AcceptedWorld config frame.initialized state ambient types live [] [] →
            AcceptedFrame config accepted frame state types →
            NestedValueOutcome config accepted frame ambient types live (.int integer)
              (evalValue fuel config frame.interpretation.environment right state) := by
          intro state currentWorld currentSource
          have rightSource : AcceptedFrame config accepted rightFrame state types := by
            simpa [rightFrame, leftFrame, ordinaryOperandFrame, sameCounter] using
              (ordinaryOperandFrame_accepted accepted frame checkFuel state types currentSource).withRootCursor rootMiddle sameRoot
          have safe := nestedScalarExpression_complete rightForm fuel config accepted rightFrame state ambient types live currentWorld rightSource
            empty globalLimit noParameters scalars (.int integer) rightRoots typingAfter rootFinal rightChecked
          exact safe.retarget config accepted frame rightFrame ambient types live (.int integer) state _ currentSource empty rfl rfl
        exact nestedValueBinary_compose fuel config accepted frame ambient types live integer operation left right origin before leftSafe' rightSafe
  | @conversion expression kind target origin operand =>
    cases fuel with
    | zero => simp [NestedValueOutcome, evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      cases nesting : frame.typingFuel with
      | zero =>
        have typed := checked.typing
        rw [nesting] at typed
        change Except.error _ = Except.ok _ at typed
        cases typed
      | succ checkFuel =>
        obtain ⟨integer, targetInt, operandRoots, operandAfter, sameTarget, sameTy, sameRoots, operandChecked⟩ :=
          checkedValue_conv_operand frame checkFuel kind target expression origin ty roots typingAfter rootsAfter nesting checked
        subst target ty roots
        let operandFrame := ordinaryOperandFrame frame checkFuel
        have operandSource := ordinaryOperandFrame_accepted accepted frame checkFuel before types source
        have safe := nestedScalarExpression_complete operand fuel config accepted operandFrame before ambient types live world operandSource
          empty globalLimit noParameters scalars (.int integer) operandRoots typingAfter operandAfter operandChecked
        have safe' : NestedValueOutcome config accepted frame ambient types live (.int integer)
            (evalValue fuel config frame.interpretation.environment expression before) :=
          safe.retarget config accepted frame operandFrame ambient types live (.int integer) before _ source empty rfl rfl
        exact nestedValueConversion_compose fuel config accepted frame ambient types live integer targetInt kind expression origin before safe'
  | @comparison left right operation leftForm rightForm =>
    cases fuel with
    | zero => simp [NestedValueOutcome, evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      cases nesting : frame.typingFuel with
      | zero =>
        have typed := checked.typing
        rw [nesting] at typed
        change Except.error _ = Except.ok _ at typed
        cases typed
      | succ checkFuel =>
        obtain ⟨operandTy, middle, leftRoots, rightRoots, rootMiddle, sameTy, sameRoots, operandKind, leftChecked, rightChecked⟩ :=
          checkedValue_cmp_operands frame checkFuel operation left right ty roots typingAfter rootsAfter nesting checked
        subst ty roots
        let leftFrame := ordinaryOperandFrame frame checkFuel
        let rightFrame := { leftFrame with
          typingCounter := middle
          rootCursor := rootMiddle }
        have leftFacts := nestedScalarExpression_cursors leftForm checkFuel leftFrame operandTy leftRoots middle rootMiddle rfl leftChecked
        have sameCounter : middle = frame.typingCounter := by simpa [leftFrame, ordinaryOperandFrame] using leftFacts.1
        have sameRoot : rootMiddle.nextVar = frame.rootCursor.nextVar := by simpa [leftFrame, ordinaryOperandFrame] using leftFacts.2
        have leftSource := ordinaryOperandFrame_accepted accepted frame checkFuel before types source
        have leftSafe := nestedScalarExpression_complete leftForm fuel config accepted leftFrame before ambient types live world leftSource
          empty globalLimit noParameters scalars operandTy leftRoots middle rootMiddle leftChecked
        have leftSafe' : NestedValueOutcome config accepted frame ambient types live operandTy
            (evalValue fuel config frame.interpretation.environment left before) :=
          leftSafe.retarget config accepted frame leftFrame ambient types live operandTy before _ source empty rfl rfl
        have rightSafe : ∀ state, AcceptedWorld config frame.initialized state ambient types live [] [] →
            AcceptedFrame config accepted frame state types →
            NestedValueOutcome config accepted frame ambient types live operandTy
              (evalValue fuel config frame.interpretation.environment right state) := by
          intro state currentWorld currentSource
          have rightSource : AcceptedFrame config accepted rightFrame state types := by
            simpa [rightFrame, leftFrame, ordinaryOperandFrame, sameCounter] using
              (ordinaryOperandFrame_accepted accepted frame checkFuel state types currentSource).withRootCursor rootMiddle sameRoot
          have safe := nestedScalarExpression_complete rightForm fuel config accepted rightFrame state ambient types live currentWorld rightSource
            empty globalLimit noParameters scalars operandTy rightRoots typingAfter rootsAfter rightChecked
          exact safe.retarget config accepted frame rightFrame ambient types live operandTy state _ currentSource empty rfl rfl
        exact nestedValueComparison_compose fuel config accepted frame ambient types live operandTy operandKind operation left right before leftSafe' rightSafe
  | @conjunction left right leftForm rightForm | @disjunction left right leftForm rightForm =>
    cases fuel with
    | zero => simp [NestedValueOutcome, evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      cases nesting : frame.typingFuel with
      | zero =>
        have typed := checked.typing
        rw [nesting] at typed
        change Except.error _ = Except.ok _ at typed
        cases typed
      | succ checkFuel =>
        obtain ⟨middle, leftRoots, rightRoots, rootMiddle, sameTy, sameRoots, leftChecked, rightChecked⟩ :=
          by
            first
            | exact shortCircuit_operands true frame checkFuel left right ty roots typingAfter rootsAfter nesting checked
            | exact shortCircuit_operands false frame checkFuel left right ty roots typingAfter rootsAfter nesting checked
        subst ty roots
        let leftFrame := ordinaryOperandFrame frame checkFuel
        let rightFrame := { leftFrame with
          typingCounter := middle
          rootCursor := rootMiddle }
        have leftFacts := nestedScalarExpression_cursors leftForm checkFuel leftFrame .bool leftRoots middle rootMiddle rfl leftChecked
        have sameCounter : middle = frame.typingCounter := by simpa [leftFrame, ordinaryOperandFrame] using leftFacts.1
        have sameRoot : rootMiddle.nextVar = frame.rootCursor.nextVar := by simpa [leftFrame, ordinaryOperandFrame] using leftFacts.2
        have leftSource := ordinaryOperandFrame_accepted accepted frame checkFuel before types source
        have leftSafe := nestedScalarExpression_complete leftForm fuel config accepted leftFrame before ambient types live world leftSource
          empty globalLimit noParameters scalars .bool leftRoots middle rootMiddle leftChecked
        have leftSafe' : NestedValueOutcome config accepted frame ambient types live .bool
            (evalValue fuel config frame.interpretation.environment left before) :=
          leftSafe.retarget config accepted frame leftFrame ambient types live .bool before _ source empty rfl rfl
        have rightSafe : ∀ state, AcceptedWorld config frame.initialized state ambient types live [] [] →
            AcceptedFrame config accepted frame state types →
            NestedValueOutcome config accepted frame ambient types live .bool
              (evalValue fuel config frame.interpretation.environment right state) := by
          intro state currentWorld currentSource
          have rightSource : AcceptedFrame config accepted rightFrame state types := by
            simpa [rightFrame, leftFrame, ordinaryOperandFrame, sameCounter] using
              (ordinaryOperandFrame_accepted accepted frame checkFuel state types currentSource).withRootCursor rootMiddle sameRoot
          have safe := nestedScalarExpression_complete rightForm fuel config accepted rightFrame state ambient types live currentWorld rightSource
            empty globalLimit noParameters scalars .bool rightRoots typingAfter rootsAfter rightChecked
          exact safe.retarget config accepted frame rightFrame ambient types live .bool state _ currentSource empty rfl rfl
        exact by
          first
          | exact nestedValueShortCircuit_compose true fuel config accepted frame ambient types live left right before leftSafe' rightSafe
          | exact nestedValueShortCircuit_compose false fuel config accepted frame ambient types live left right before leftSafe' rightSafe
  | @conditional condition yes no origin conditionForm yesForm noForm =>
    cases fuel with
    | zero => simpa [NestedValueOutcome, evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState] using And.intro world (And.intro source True.intro)
    | succ fuel =>
      cases nesting : frame.typingFuel with
      | zero =>
        have typed := checked.typing
        rw [nesting] at typed
        change Except.error _ = Except.ok _ at typed
        cases typed
      | succ checkFuel =>
        obtain ⟨conditionTyping, conditionRoots, conditionCursor, yesTypes, yesTyping, yesResult, yesCursor,
          noTypes, noTyping, noResult, conditionChecked, yesChecked, noChecked⟩ :=
          checkedValue_conditional_children frame checkFuel condition yes no origin ty roots typingAfter rootsAfter nesting checked
        let conditionFrame := ordinaryOperandFrame frame checkFuel
        let yesFrame := { frame with
          typingFuel := checkFuel
          typingCounter := conditionTyping
          rootCursor := conditionCursor }
        let noFrame := { frame with
          typingFuel := checkFuel
          typingCounter := yesTyping
          rootCursor := yesCursor }
        have conditionFacts := nestedScalarExpression_cursors conditionForm checkFuel conditionFrame .bool conditionRoots conditionTyping conditionCursor rfl conditionChecked
        have yesFacts := nestedScalarBlock_cursors yesForm checkFuel yesFrame yesTypes yesTyping yesResult yesCursor rfl yesChecked
        have conditionCounter : conditionTyping = frame.typingCounter := by simpa [conditionFrame, ordinaryOperandFrame] using conditionFacts.1
        have conditionRoot : conditionCursor.nextVar = frame.rootCursor.nextVar := by simpa [conditionFrame, ordinaryOperandFrame] using conditionFacts.2
        have yesCounter : yesTyping = frame.typingCounter := by simpa [yesFrame, conditionCounter] using yesFacts.1
        have yesRoot : yesCursor.nextVar = frame.rootCursor.nextVar := by simpa [yesFrame, conditionRoot] using yesFacts.2
        obtain ⟨yesTy, yesSingleton⟩ := nestedScalarBlock_singleton yesForm checkFuel yesFrame.typing yesFrame.typingCounter yesTyping yesTypes yesChecked.typing
        obtain ⟨noTy, noSingleton⟩ := nestedScalarBlock_singleton noForm checkFuel noFrame.typing noFrame.typingCounter noTyping noTypes noChecked.typing
        subst yesTypes noTypes
        have typed := checked.typing
        rw [nesting] at typed
        have alignment := typeExpr_if_nonEscaping_types checkFuel frame.typing condition yes no origin frame.typingCounter typingAfter
          conditionTyping yesTyping noTyping ty yesTy noTy typed conditionChecked.typing yesChecked.typing noChecked.typing
          (nestedScalarBlock_notEscapes yesForm checkFuel) (nestedScalarBlock_notEscapes noForm checkFuel)
        obtain ⟨yesEq, noEq⟩ := alignment
        subst yesTy noTy
        have conditionSource := ordinaryOperandFrame_accepted accepted frame checkFuel before types source
        have conditionSafe := nestedScalarExpression_complete conditionForm fuel config accepted conditionFrame before ambient types live
          world conditionSource empty globalLimit noParameters scalars .bool conditionRoots conditionTyping conditionCursor conditionChecked
        have conditionSafe' : NestedValueOutcome config accepted frame ambient types live .bool
            (evalValue fuel config frame.interpretation.environment condition before) :=
          conditionSafe.retarget config accepted frame conditionFrame ambient types live .bool before _ source empty rfl rfl
        have yesSafe : ∀ state, AcceptedWorld config frame.initialized state ambient types live [] [] →
            AcceptedFrame config accepted frame state types →
            NestedBlockOutcome config accepted frame ambient types live ty
              (execBlock fuel config frame.interpretation.environment [] [] yes state) := by
          intro state currentWorld currentSource
          have branchSource : AcceptedFrame config accepted yesFrame state types := by
            simpa [yesFrame, conditionCounter] using (currentSource.withRootCursor conditionCursor conditionRoot).withTypingFuel checkFuel
          have safe := nestedScalarBlock_complete yesForm fuel config accepted yesFrame state ambient types live currentWorld branchSource
            empty globalLimit noParameters scalars ty yesTyping yesResult yesCursor yesChecked
          exact safe.retarget config accepted frame yesFrame ambient types live ty state _ currentSource empty rfl rfl
        have noSafe : ∀ state, AcceptedWorld config frame.initialized state ambient types live [] [] →
            AcceptedFrame config accepted frame state types →
            NestedBlockOutcome config accepted frame ambient types live ty
              (execBlock fuel config frame.interpretation.environment [] [] no state) := by
          intro state currentWorld currentSource
          have branchSource : AcceptedFrame config accepted noFrame state types := by
            simpa [noFrame, yesCounter] using (currentSource.withRootCursor yesCursor yesRoot).withTypingFuel checkFuel
          have safe := nestedScalarBlock_complete noForm fuel config accepted noFrame state ambient types live currentWorld branchSource
            empty globalLimit noParameters scalars ty noTyping noResult rootsAfter noChecked
          exact safe.retarget config accepted frame noFrame ambient types live ty state _ currentSource empty rfl rfl
        exact nestedValueConditional_compose fuel config accepted frame ambient types live ty condition yes no origin before conditionSafe' yesSafe noSafe
termination_by fuel

theorem nestedScalarBlock_complete {block : Block} (form : NestedScalarBlock block)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config frame.initialized before ambient types live [] [])
    (source : AcceptedFrame config accepted frame before types) (empty : frame.interpretation.environment.vars = #[])
    (globalLimit : frame.typing.globalLimit ≤ frame.initialized)
    (noParameters : ∀ parameter global, ¬ frame.interpretation.parameters parameter (.global global))
    (scalars : FlatGlobalsAreScalar config) (ty : Ty) (typingAfter : Nat) (result : List RootRef × (Nat × Nat)) (rootsAfter : RState)
    (checked : CheckedConditionalBlock frame block [ty] typingAfter result rootsAfter) :
    NestedBlockOutcome config accepted frame ambient types live ty (execBlock fuel config frame.interpretation.environment [] [] block before) := by
  cases form with
  | block scope statements tail statementsForm tailForm =>
    cases fuel with
    | zero => simpa [NestedBlockOutcome, execBlock, timeout, EvalM.stop, Goose.Proofs.Exit.stepState] using And.intro world (And.intro source True.intro)
    | succ fuel =>
      cases nesting : frame.typingFuel with
      | zero =>
        have typed := checked.typing
        rw [nesting] at typed
        change Except.error _ = Except.ok _ at typed
        cases typed
      | succ checkFuel =>
        obtain ⟨next, typingMiddle, rootsMiddle, tailRoots, statementsTyped, statementsRooted, statementsAvailable, tailChecked⟩ :=
          checkedConditionalBlock_tail frame checkFuel scope before.nextScope statements tail ty typingAfter result rootsAfter nesting checked
        let child := emptyChildScopeFrame frame scope before.nextScope checkFuel
        let entered := { before with nextScope := before.nextScope + 1 }
        let tailFrame := { child with
          typing := next
          typingCounter := typingMiddle
          rootCursor := rootsMiddle }
        have statementFacts := nestedScalarStatements_cursors statementsForm checkFuel child next typingMiddle rootsMiddle rfl
          statementsTyped statementsRooted statementsAvailable
        have enteredWorld := (freshScope_acceptedWorld config frame.initialized before ambient types live world).2
        have enteredSource := source.enterEmptyScope empty scope checkFuel
        have statementsSafe := nestedScalarStatements_complete statementsForm fuel config accepted child entered ambient types live
          enteredWorld enteredSource empty globalLimit noParameters scalars next typingMiddle rootsMiddle statementsTyped statementsRooted statementsAvailable
        have tailSafe : ∀ state, AcceptedWorld config frame.initialized state ambient types live [] [] →
            AcceptedFrame config accepted child state types →
            NestedValueOutcome config accepted child ambient types live ty (evalValue fuel config child.interpretation.environment tail state) := by
          intro state currentWorld currentSource
          have tailSource : AcceptedFrame config accepted tailFrame state types := by
            simpa [tailFrame, statementFacts.1, statementFacts.2.1] using currentSource.withRootCursor rootsMiddle statementFacts.2.2
          have safe := nestedScalarExpression_complete tailForm fuel config accepted tailFrame state ambient types live currentWorld tailSource
            empty (by simpa [tailFrame, child, emptyChildScopeFrame, statementFacts.1] using globalLimit) noParameters scalars ty tailRoots typingAfter rootsAfter tailChecked
          exact safe.retarget config accepted child tailFrame ambient types live ty state _ currentSource empty rfl rfl
        exact nestedBlock_compose fuel checkFuel config accepted frame ambient types live ty scope statements tail before source empty statementsSafe tailSafe
termination_by fuel

theorem nestedScalarStatements_complete {statements : List Stmt} (form : NestedScalarStatements statements)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config frame.initialized before ambient types live [] [])
    (source : AcceptedFrame config accepted frame before types) (empty : frame.interpretation.environment.vars = #[])
    (globalLimit : frame.typing.globalLimit ≤ frame.initialized)
    (noParameters : ∀ parameter global, ¬ frame.interpretation.parameters parameter (.global global))
    (scalars : FlatGlobalsAreScalar config) (next : TypingEnv) (typingAfter : Nat) (rootsAfter : RState)
    (typed : typeStatements frame.typingFuel frame.typing statements frame.typingCounter = .ok (next, typingAfter))
    (rooted : rpStmts frame.source statements frame.rootCursor = .ok ((), rootsAfter))
    (available : GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff) :
    NestedStatementsOutcome config accepted frame ambient types live (execStmts fuel config frame.interpretation.environment statements before) := by
  cases form with
  | nil =>
    cases fuel <;> simp [NestedStatementsOutcome, execStmts, timeout, EvalM.stop, pure, Goose.Proofs.Exit.stepState, world, source]
  | expression expression origin rest expressionForm tailForm =>
    cases fuel with
    | zero => simp [NestedStatementsOutcome, execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      obtain ⟨rootMiddle, headRooted, tailRooted⟩ := rpStmts_cons rooted
      obtain ⟨operandRoots, operandRooted⟩ := rpStmt_expression headRooted
      have headAvailable : GlobalEffectsAvailable frame.interpretation frame.initialized rootMiddle.eff := by
        have included := rpStmts_effectTargetsIncluded tailRooted
        intro target member global instantiates
        exact available target (included member) global instantiates
      cases nesting : frame.typingFuel with
      | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
      | succ headFuel =>
        cases headFuel with
        | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
        | succ checkFuel =>
          have allTyped := typed
          rw [nesting] at allTyped
          simp only [typeStatements, bind, StateT.bind] at allTyped
          obtain ⟨result, headTyped, tailTyped⟩ := nestedComplete_bind_success _ _ _ allTyped
          obtain ⟨headEnvironment, headCounter⟩ := result
          obtain ⟨sameEnv, operandTypes, operandTyped⟩ := typeStatement_expression_parts checkFuel frame.typing headEnvironment
            expression origin frame.typingCounter headCounter headTyped
          obtain ⟨ty, sameTypes⟩ := nestedScalarExpression_singleton expressionForm checkFuel
            (ordinaryOperandFrame frame checkFuel).typing frame.typingCounter headCounter operandTypes operandTyped
          subst operandTypes
          have operandChecked : CheckedValue (ordinaryOperandFrame frame checkFuel) expression ty operandRoots headCounter rootMiddle :=
            ⟨operandTyped, operandRooted, headAvailable⟩
          have cursor := nestedScalarExpression_cursors expressionForm checkFuel (ordinaryOperandFrame frame checkFuel)
            ty operandRoots headCounter rootMiddle rfl operandChecked
          have sameCounter : headCounter = frame.typingCounter := by simpa [ordinaryOperandFrame] using cursor.1
          have sameRoot : rootMiddle.nextVar = frame.rootCursor.nextVar := by simpa [ordinaryOperandFrame] using cursor.2
          let tailFrame := { frame with
            typingFuel := checkFuel + 1
            typing := headEnvironment
            typingCounter := headCounter
            rootCursor := rootMiddle }
          have headSafe : NestedStatementsOutcome config accepted frame ambient types live
              (execStmt fuel config frame.interpretation.environment (.expr expression origin) before) := by
            cases fuel with
            | zero => simp [NestedStatementsOutcome, execStmt, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
            | succ fuel =>
              let operandFrame := ordinaryOperandFrame frame checkFuel
              have operandSource := ordinaryOperandFrame_accepted accepted frame checkFuel before types source
              have safe := nestedScalarExpression_complete expressionForm fuel config accepted operandFrame before ambient types live world operandSource
                empty globalLimit noParameters scalars ty operandRoots headCounter rootMiddle operandChecked
              have safe' : NestedValueOutcome config accepted frame ambient types live ty
                  (evalValue fuel config frame.interpretation.environment expression before) :=
                safe.retarget config accepted frame operandFrame ambient types live ty before _ source empty rfl rfl
              exact nestedExpressionStatement_compose fuel config accepted frame ambient types live ty expression origin before safe'
          have tailSafe : ∀ state, AcceptedWorld config frame.initialized state ambient types live [] [] →
              AcceptedFrame config accepted frame state types →
              NestedStatementsOutcome config accepted frame ambient types live
                (execStmts fuel config frame.interpretation.environment rest state) := by
            intro state currentWorld currentSource
            have tailSource : AcceptedFrame config accepted tailFrame state types := by
              simpa [tailFrame, sameEnv, sameCounter] using (currentSource.withRootCursor rootMiddle sameRoot).withTypingFuel (checkFuel + 1)
            have safe := nestedScalarStatements_complete tailForm fuel config accepted tailFrame state ambient types live currentWorld tailSource
              empty (by simpa [tailFrame, sameEnv] using globalLimit) noParameters scalars next typingAfter rootsAfter tailTyped tailRooted available
            exact safe.retarget config accepted frame tailFrame ambient types live state _ currentSource empty rfl rfl
          exact nestedStatements_cons_compose fuel config accepted frame ambient types live (.expr expression origin) rest before headSafe tailSafe
  | assign id expression origin rest expressionForm tailForm =>
    cases fuel with
    | zero => simp [NestedStatementsOutcome, execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      obtain ⟨rootMiddle, headRooted, tailRooted⟩ := rpStmts_cons rooted
      have headAvailable : GlobalEffectsAvailable frame.interpretation frame.initialized rootMiddle.eff := by
        have included := rpStmts_effectTargetsIncluded tailRooted
        intro target member global instantiates
        exact available target (included member) global instantiates
      cases nesting : frame.typingFuel with
      | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
      | succ headFuel =>
        cases headFuel with
        | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
        | succ checkFuel =>
          have allTyped := typed
          rw [nesting] at allTyped
          simp only [typeStatements, bind, StateT.bind] at allTyped
          obtain ⟨result, headTyped, tailTyped⟩ := nestedComplete_bind_success _ _ _ allTyped
          obtain ⟨headEnvironment, headCounter⟩ := result
          obtain ⟨descriptor, operandRoots, operandCounter, operandCursor, declared, inside, mutable, flat, sameEnv, sameAfter, operandChecked⟩ :=
            checkedValue_nestedGlobalAssign_operand checkFuel frame id expression origin expressionForm headEnvironment headCounter rootMiddle
              headTyped headRooted headAvailable
          have moduleDeclared : config.module.globals[id]? = some descriptor := by
            rw [← source.compatible.module]
            exact declared
          have earlier : id < frame.initialized := by omega
          have cursor := nestedScalarExpression_cursors expressionForm checkFuel (scalarAssignmentOperandFrame frame checkFuel)
            descriptor.ty operandRoots operandCounter operandCursor rfl operandChecked
          have nextVar := rpStmt_directAssign_cursor frame.source (.global id) expression origin frame.rootCursor rootMiddle operandCursor
            operandRoots (Or.inr ⟨id, rfl⟩) operandChecked.provenance headRooted
          have sameRoot : rootMiddle.nextVar = frame.rootCursor.nextVar := by
            rw [nextVar]
            simpa [scalarAssignmentOperandFrame, ordinaryOperandFrame] using cursor.2
          have sameCounter : headCounter = frame.typingCounter := by
            rw [sameAfter]
            simpa [scalarAssignmentOperandFrame, ordinaryOperandFrame] using cursor.1
          let tailFrame := { frame with
            typingFuel := checkFuel + 1
            typing := headEnvironment
            typingCounter := headCounter
            rootCursor := rootMiddle }
          have headSafe : NestedStatementsOutcome config accepted frame ambient types live
              (execStmt fuel config frame.interpretation.environment (.assign (.global id) expression origin) before) := by
            cases fuel with
            | zero => simp [NestedStatementsOutcome, execStmt, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
            | succ fuel =>
              cases fuel with
              | zero => simp [NestedStatementsOutcome, execStmt, evalPlace, timeout, EvalM.stop, bind, Goose.Proofs.Exit.stepState, world, source]
              | succ fuel =>
                let operandFrame := scalarAssignmentOperandFrame frame checkFuel
                have operandSource : AcceptedFrame config accepted operandFrame before types :=
                  (ordinaryOperandFrame_accepted accepted frame checkFuel before types source).withRootCursor _ rfl
                have safe := nestedScalarExpression_complete expressionForm (fuel + 1) config accepted operandFrame before ambient types live
                  world operandSource empty globalLimit noParameters scalars descriptor.ty operandRoots operandCounter operandCursor operandChecked
                have safe' : NestedValueOutcome config accepted frame ambient types live descriptor.ty
                    (evalValue (fuel + 1) config frame.interpretation.environment expression before) :=
                  safe.retarget config accepted frame operandFrame ambient types live descriptor.ty before _ source empty rfl rfl
                exact nestedGlobalAssign_compose fuel config accepted frame ambient types live id descriptor expression origin before
                  earlier moduleDeclared (scalars id descriptor moduleDeclared flat) safe'
          have tailSafe : ∀ state, AcceptedWorld config frame.initialized state ambient types live [] [] →
              AcceptedFrame config accepted frame state types →
              NestedStatementsOutcome config accepted frame ambient types live
                (execStmts fuel config frame.interpretation.environment rest state) := by
            intro state currentWorld currentSource
            have tailSource : AcceptedFrame config accepted tailFrame state types := by
              simpa [tailFrame, sameEnv, sameCounter] using (currentSource.withRootCursor rootMiddle sameRoot).withTypingFuel (checkFuel + 1)
            have safe := nestedScalarStatements_complete tailForm fuel config accepted tailFrame state ambient types live currentWorld tailSource
              empty (by simpa [tailFrame, sameEnv] using globalLimit) noParameters scalars next typingAfter rootsAfter tailTyped tailRooted available
            exact safe.retarget config accepted frame tailFrame ambient types live state _ currentSource empty rfl rfl
          exact nestedStatements_cons_compose fuel config accepted frame ambient types live (.assign (.global id) expression origin) rest before headSafe tailSafe
termination_by fuel
end

#print axioms nestedScalarExpression_complete
#print axioms nestedScalarBlock_complete
#print axioms nestedScalarStatements_complete
end Goose.Proofs.ConstructionAcceptedExecution

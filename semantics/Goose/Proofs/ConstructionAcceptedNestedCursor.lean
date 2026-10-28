import Goose.Proofs.ConstructionAcceptedNestedAssignChecker

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private theorem nestedCursor_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

mutual
theorem nestedScalarExpression_cursors {expression : Expr} (form : NestedScalarExpression expression)
    (fuel : Nat) (frame : ConstructionSourceFrame) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState) (fuelAt : frame.typingFuel = fuel)
    (checked : CheckedValue frame expression ty roots typingAfter rootsAfter) :
    typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar := by
  cases form with
  | scalar form => exact checked_binary_recursive_cursor form frame ty roots typingAfter rootsAfter checked
  | conditional origin conditionForm yesForm noForm =>
    cases fuel with
    | zero =>
      have typed := checked.typing
      rw [fuelAt] at typed
      change Except.error _ = Except.ok _ at typed
      cases typed
    | succ fuel =>
      obtain ⟨conditionTyping, conditionRoots, conditionCursor, yesTypes, yesTyping, yesResult, yesCursor,
        noTypes, noTyping, noResult, conditionChecked, yesChecked, noChecked⟩ :=
        checkedValue_conditional_children frame fuel _ _ _ origin ty roots typingAfter rootsAfter fuelAt checked
      have conditionFacts := nestedScalarExpression_cursors conditionForm fuel (ordinaryOperandFrame frame fuel) .bool
        conditionRoots conditionTyping conditionCursor rfl conditionChecked
      have yesFacts := nestedScalarBlock_cursors yesForm fuel _ yesTypes yesTyping yesResult yesCursor rfl yesChecked
      have noFacts := nestedScalarBlock_cursors noForm fuel _ noTypes noTyping noResult rootsAfter rfl noChecked
      have typed := checked.typing
      rw [fuelAt] at typed
      obtain ⟨otherCondition, otherYesTypes, otherYesAfter, otherNoTypes, otherNoAfter, conditionTyped, yesTyped, noTyped⟩ :=
        typeExpr_if_branches fuel frame.typing _ _ _ origin frame.typingCounter typingAfter [ty] typed
      have conditionSame : otherCondition = conditionTyping := by
        have pair := conditionTyped.symm.trans conditionChecked.typing
        exact (Prod.mk.inj (Except.ok.inj pair)).2
      subst otherCondition
      have yesSame : otherYesAfter = yesTyping := by
        have pair := yesTyped.symm.trans yesChecked.typing
        exact (Prod.mk.inj (Except.ok.inj pair)).2
      subst otherYesAfter
      have noSame : otherNoAfter = noTyping := by
        have pair := noTyped.symm.trans noChecked.typing
        exact (Prod.mk.inj (Except.ok.inj pair)).2
      subst otherNoAfter
      have resultEq := (typeExpr_if_nonEscaping_cursor fuel frame.typing _ _ _ origin frame.typingCounter typingAfter
        conditionTyping yesTyping noTyping [ty] otherYesTypes otherNoTypes typed conditionTyped yesTyped noTyped
        (nestedScalarBlock_notEscapes yesForm fuel) (nestedScalarBlock_notEscapes noForm fuel)).2
      constructor
      · simpa [ordinaryOperandFrame] using resultEq.trans (noFacts.1.trans (yesFacts.1.trans conditionFacts.1))
      · simpa [ordinaryOperandFrame] using noFacts.2.trans (yesFacts.2.trans conditionFacts.2)
termination_by fuel

theorem nestedScalarBlock_cursors {block : Block} (form : NestedScalarBlock block)
    (fuel : Nat) (frame : ConstructionSourceFrame) (types : List Ty) (typingAfter : Nat)
    (result : List RootRef × (Nat × Nat)) (rootsAfter : RState) (fuelAt : frame.typingFuel = fuel)
    (checked : CheckedConditionalBlock frame block types typingAfter result rootsAfter) :
    typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar := by
  have typed := checked.typing
  rw [fuelAt] at typed
  obtain ⟨ty, sameTypes⟩ := nestedScalarBlock_singleton form fuel frame.typing frame.typingCounter typingAfter types typed
  subst types
  cases form with
  | block scope statements tail statementsForm tailForm =>
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      obtain ⟨next, typingMiddle, rootsMiddle, roots, statementsTyped, statementsRooted, statementsAvailable, tailChecked⟩ :=
        checkedConditionalBlock_tail frame fuel scope 0 statements tail ty typingAfter result rootsAfter fuelAt checked
      let bodyFrame := emptyChildScopeFrame frame scope 0 fuel
      let tailFrame := { bodyFrame with
        typing := next
        typingCounter := typingMiddle
        rootCursor := rootsMiddle }
      have statementFacts := nestedScalarStatements_cursors statementsForm fuel bodyFrame next typingMiddle rootsMiddle rfl
        statementsTyped statementsRooted statementsAvailable
      have tailFacts := nestedScalarExpression_cursors tailForm fuel tailFrame ty roots typingAfter rootsAfter rfl tailChecked
      constructor
      · simpa [tailFrame, bodyFrame, emptyChildScopeFrame] using tailFacts.1.trans statementFacts.2.1
      · simpa [tailFrame, bodyFrame, emptyChildScopeFrame] using tailFacts.2.trans statementFacts.2.2
termination_by fuel

theorem nestedScalarStatements_cursors {statements : List Stmt} (form : NestedScalarStatements statements)
    (fuel : Nat) (frame : ConstructionSourceFrame) (next : TypingEnv) (typingAfter : Nat) (rootsAfter : RState)
    (fuelAt : frame.typingFuel = fuel)
    (typed : typeStatements fuel frame.typing statements frame.typingCounter = .ok (next, typingAfter))
    (rooted : rpStmts frame.source statements frame.rootCursor = .ok ((), rootsAfter))
    (available : GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff) :
    next = frame.typing ∧ typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar := by
  cases form with
  | nil =>
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      change Except.ok (frame.typing, frame.typingCounter) = Except.ok (next, typingAfter) at typed
      change Except.ok ((), frame.rootCursor) = Except.ok ((), rootsAfter) at rooted
      cases typed
      cases rooted
      exact ⟨rfl, rfl, rfl⟩
  | expression expression origin rest expressionForm tailForm =>
    obtain ⟨rootMiddle, headRooted, tailRooted⟩ := rpStmts_cons rooted
    obtain ⟨operandRoots, operandRooted⟩ := rpStmt_expression headRooted
    have headAvailable : GlobalEffectsAvailable frame.interpretation frame.initialized rootMiddle.eff := by
      have included := rpStmts_effectTargetsIncluded tailRooted
      intro target member global instantiates
      exact available target (included member) global instantiates
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ headFuel =>
      cases headFuel with
      | zero => change Except.error _ = Except.ok _ at typed; cases typed
      | succ checkFuel =>
        simp only [typeStatements, bind, StateT.bind] at typed
        obtain ⟨result, headTyped, tailTyped⟩ := nestedCursor_bind_success _ _ _ typed
        obtain ⟨headEnvironment, headCounter⟩ := result
        obtain ⟨sameEnv, operandTypes, operandTyped⟩ := typeStatement_expression_parts checkFuel frame.typing headEnvironment
          expression origin frame.typingCounter headCounter headTyped
        obtain ⟨ty, sameTypes⟩ := nestedScalarExpression_singleton expressionForm checkFuel
          (ordinaryOperandFrame frame checkFuel).typing frame.typingCounter headCounter operandTypes operandTyped
        subst operandTypes
        have checked : CheckedValue (ordinaryOperandFrame frame checkFuel) expression ty operandRoots headCounter rootMiddle :=
          ⟨operandTyped, operandRooted, headAvailable⟩
        have headFacts := nestedScalarExpression_cursors expressionForm checkFuel (ordinaryOperandFrame frame checkFuel)
          ty operandRoots headCounter rootMiddle rfl checked
        let middleFrame := { frame with
          typingFuel := checkFuel + 1
          typing := headEnvironment
          typingCounter := headCounter
          rootCursor := rootMiddle }
        have tailFacts := nestedScalarStatements_cursors tailForm (checkFuel + 1) middleFrame next typingAfter rootsAfter rfl
          tailTyped tailRooted available
        constructor
        · simpa [middleFrame, sameEnv] using tailFacts.1
        constructor
        · simpa [middleFrame, ordinaryOperandFrame] using tailFacts.2.1.trans headFacts.1
        · simpa [middleFrame, ordinaryOperandFrame] using tailFacts.2.2.trans headFacts.2
  | assign id expression origin rest expressionForm tailForm =>
    obtain ⟨rootMiddle, headRooted, tailRooted⟩ := rpStmts_cons rooted
    have headAvailable : GlobalEffectsAvailable frame.interpretation frame.initialized rootMiddle.eff := by
      have included := rpStmts_effectTargetsIncluded tailRooted
      intro target member global instantiates
      exact available target (included member) global instantiates
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ headFuel =>
      cases headFuel with
      | zero => change Except.error _ = Except.ok _ at typed; cases typed
      | succ checkFuel =>
        simp only [typeStatements, bind, StateT.bind] at typed
        obtain ⟨result, headTyped, tailTyped⟩ := nestedCursor_bind_success _ _ _ typed
        obtain ⟨headEnvironment, headCounter⟩ := result
        obtain ⟨descriptor, operandRoots, operandCounter, operandCursor, declared, inside, mutable, sameEnv, sameAfter, checked⟩ :=
          checkedValue_nestedGlobalAssign_operand checkFuel frame id expression origin expressionForm headEnvironment headCounter rootMiddle
            headTyped headRooted headAvailable
        have operandFacts := nestedScalarExpression_cursors expressionForm checkFuel (scalarAssignmentOperandFrame frame checkFuel)
          descriptor.ty operandRoots operandCounter operandCursor rfl checked
        have nextVar := rpStmt_directAssign_cursor frame.source (.global id) expression origin frame.rootCursor rootMiddle operandCursor
          operandRoots (Or.inr ⟨id, rfl⟩) checked.provenance headRooted
        have sameRoot : rootMiddle.nextVar = frame.rootCursor.nextVar := by
          rw [nextVar]
          simpa [scalarAssignmentOperandFrame, ordinaryOperandFrame] using operandFacts.2
        have sameCounter : headCounter = frame.typingCounter := by
          rw [sameAfter]
          simpa [scalarAssignmentOperandFrame, ordinaryOperandFrame] using operandFacts.1
        let middleFrame := { frame with
          typingFuel := checkFuel + 1
          typing := headEnvironment
          typingCounter := headCounter
          rootCursor := rootMiddle }
        have tailFacts := nestedScalarStatements_cursors tailForm (checkFuel + 1) middleFrame next typingAfter rootsAfter rfl
          tailTyped tailRooted available
        constructor
        · simpa [middleFrame, sameEnv] using tailFacts.1
        constructor
        · simpa [middleFrame, sameCounter] using tailFacts.2.1
        · simpa [middleFrame, sameRoot] using tailFacts.2.2
termination_by fuel
end

#print axioms nestedScalarExpression_cursors
#print axioms nestedScalarBlock_cursors
#print axioms nestedScalarStatements_cursors
end Goose.Proofs.ConstructionAcceptedExecution

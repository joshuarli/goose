import Goose.Proofs.ConstructionAcceptedScalarEffectSequence
import Goose.Proofs.ConstructionAcceptedConditionalBranches

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership

private theorem globalSequence_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem typeStatement_expression_parts (fuel : Nat) (environment next : TypingEnv) (expression : Expr) (origin : Nat)
    (before after : Nat) (checked : typeStatement (fuel + 1) environment (.expr expression origin) before = .ok (next, after)) :
    next = environment ∧ ∃ types, typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
      expression before = .ok (types, after) := by
  simp only [typeStatement, bind, StateT.bind] at checked
  change (Except.bind (typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
    expression before) _) = _ at checked
  obtain ⟨result, operand, remaining⟩ := globalSequence_bind_success _ _ _ checked
  obtain ⟨types, counter⟩ := result
  obtain ⟨result, required, returned⟩ := globalSequence_bind_success _ _ _ remaining
  cases returned
  cases fixed : types.all (fun ty => !ty.nonfixed) with
  | false =>
    simp only [fixed] at required
    change Except.error _ = Except.ok _ at required
    cases required
  | true =>
    simp only [fixed] at required
    change Except.ok ((), counter) = Except.ok result at required
    cases required
    exact ⟨rfl, types, operand⟩

theorem scalarExpressionStatements_effects_bounded {statements : List Stmt} (form : ScalarExpressionStatements statements) :
    ∀ (fuel : Nat) (environment next : TypingEnv) (source : PEnv) (count beforeCounter afterCounter : Nat)
      (before after : RState),
      environment.globalLimit ≤ count → GlobalEffectTargetsBounded before.eff count →
      typeStatements fuel environment statements beforeCounter = .ok (next, afterCounter) →
      rpStmts source statements before = .ok ((), after) →
      next = environment ∧ GlobalEffectTargetsBounded after.eff count := by
  induction form with
  | nil =>
    intro fuel environment next source count beforeCounter afterCounter before after limit bounded typed rooted
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      change Except.ok (environment, beforeCounter) = Except.ok (next, afterCounter) at typed
      change Except.ok ((), before) = Except.ok ((), after) at rooted
      cases typed
      cases rooted
      exact ⟨rfl, bounded⟩
  | cons expression origin rest expressionForm tail ih =>
    intro fuel environment next source count beforeCounter afterCounter before after limit bounded typed rooted
    obtain ⟨middle, headRooted, tailRooted⟩ := rpStmts_cons rooted
    obtain ⟨operandRoots, operandRooted⟩ := rpStmt_expression headRooted
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      simp only [typeStatements, bind, StateT.bind] at typed
      obtain ⟨result, headTyped, tailTyped⟩ := globalSequence_bind_success _ _ _ typed
      obtain ⟨headEnvironment, headCounter⟩ := result
      cases fuel with
      | zero => change Except.error _ = Except.ok _ at headTyped; cases headTyped
      | succ checkFuel =>
        obtain ⟨same, operandTypes, operandTyped⟩ :=
          typeStatement_expression_parts checkFuel environment headEnvironment expression origin beforeCounter headCounter headTyped
        subst headEnvironment
        have middleBound := recursiveScalar_effects_bounded expressionForm checkFuel
          { environment with use := .ordinary, request := .value, resultRequests := [] } source count
          beforeCounter headCounter before middle operandTypes operandRoots limit bounded operandTyped operandRooted
        exact ih (checkFuel + 1) environment next source count headCounter afterCounter middle after limit middleBound tailTyped tailRooted

theorem scalarExpressionStatements_checked {statements : List Stmt} (form : ScalarExpressionStatements statements) :
    ∀ (frame : ConstructionSourceFrame) (next : TypingEnv) (typingAfter : Nat) (rootsAfter : RState),
      typeStatements frame.typingFuel frame.typing statements frame.typingCounter = .ok (next, typingAfter) →
      rpStmts frame.source statements frame.rootCursor = .ok ((), rootsAfter) →
      GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff →
      CheckedScalarStatements frame statements := by
  induction form with
  | nil =>
    intro frame next typingAfter rootsAfter typed rooted available
    exact .nil frame
  | cons expression origin rest expressionForm tail ih =>
    intro frame next typingAfter rootsAfter typed rooted available
    obtain ⟨rootMiddle, headRooted, tailRooted⟩ := rpStmts_cons rooted
    obtain ⟨roots, expressionRooted⟩ := rpStmt_expression headRooted
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
        obtain ⟨result, headTyped, tailTyped⟩ := globalSequence_bind_success _ _ _ allTyped
        obtain ⟨headEnvironment, headCounter⟩ := result
        obtain ⟨same, operandTypes, operandTyped⟩ := typeStatement_expression_parts checkFuel frame.typing headEnvironment
          expression origin frame.typingCounter headCounter headTyped
        obtain ⟨ty, sameTypes⟩ := typeExpr_scalar_singleton expressionForm checkFuel
          (ordinaryOperandFrame frame checkFuel).typing frame.typingCounter headCounter operandTypes operandTyped
        subst operandTypes
        have checked : CheckedValue (ordinaryOperandFrame frame checkFuel) expression ty roots headCounter rootMiddle :=
          ⟨operandTyped, expressionRooted, headAvailable⟩
        let nextFrame := { frame with
          typingFuel := checkFuel + 1
          typing := headEnvironment
          typingCounter := headCounter
          rootCursor := rootMiddle }
        have remaining := ih nextFrame next typingAfter rootsAfter tailTyped tailRooted available
        exact .cons frame expression origin rest checkFuel ty roots headCounter rootMiddle headEnvironment headCounter rootMiddle nesting
          expressionForm checked headTyped headRooted remaining

theorem execStmts_checkedScalar_initializer {frame : ConstructionSourceFrame} {statements : List Stmt}
    (checkedStatements : CheckedScalarStatements frame statements) :
    ∀ (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (state : ExecutionState)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
      (regions : List ReceivingRegion) (pending : List PendingCarrierFrame),
      AcceptedWorld config frame.initialized state ambient types live regions pending →
      AcceptedFrame config accepted frame state types →
      let outcome := execStmts fuel config frame.interpretation.environment statements state
      Goose.Proofs.Exit.stepState outcome = state ∧
        (∀ flow after, outcome = .ok flow after → flow = .normal .unit ∧ after = state) ∧
        AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
        AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types := by
  induction checkedStatements with
  | nil frame =>
    intro fuel config accepted state ambient types live regions pending world source
    cases fuel <;> simp [execStmts, timeout, EvalM.stop, pure, Goose.Proofs.Exit.stepState, world, source]
  | cons frame expression origin rest checkFuel ty roots typingAfter rootsAfter next statementAfter statementRootsAfter nesting form checked typed rooted tail ih =>
    intro fuel config accepted state ambient types live regions pending world source
    cases fuel with
    | zero => simp [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      let nextFrame := { frame with typingFuel := checkFuel + 1, typing := next, typingCounter := statementAfter, rootCursor := statementRootsAfter }
      obtain ⟨sameTyping, sameCounter, nextSource⟩ := checkedScalarExpression_statementAdvance config accepted frame state types source
        expression origin form checkFuel ty roots typingAfter rootsAfter checked next statementAfter statementRootsAfter typed rooted
      have head := execStmt_checkedScalarExpression_complete expression origin form fuel checkFuel config accepted frame state
        ambient types live regions pending world source ty roots typingAfter rootsAfter checked
      cases executed : execStmt fuel config frame.interpretation.environment (.expr expression origin) state with
      | stop reason after | escape reason carriers after | jump reason kind after =>
        simp only [executed, Goose.Proofs.Exit.stepState] at head
        have same := head.1
        subst after
        simp only [execStmts, bind, executed, Goose.Proofs.Exit.stepState, reduceCtorEq, true_and]
        exact ⟨fun _ _ impossible => False.elim impossible, world, source⟩
      | ok flow after =>
        obtain ⟨sameFlow, sameAfter⟩ := head.2.1 flow after executed
        subst flow after
        have nextWorld : AcceptedWorld config nextFrame.initialized state ambient types live regions pending := world
        have final := ih fuel config accepted state ambient types live regions pending nextWorld nextSource
        change Goose.Proofs.Exit.stepState (execStmts fuel config frame.interpretation.environment rest state) = state ∧
          (∀ flow after, execStmts fuel config frame.interpretation.environment rest state = .ok flow after → _) ∧ _ at final
        simp only [execStmts, bind, executed]
        exact ⟨final.1, final.2.1, by simpa only [final.1] using world, by simpa only [final.1] using source⟩

theorem checkedScalarStatements_finalFrame {frame : ConstructionSourceFrame} {statements : List Stmt}
    (checkedStatements : CheckedScalarStatements frame statements) :
    ∀ (config : EvalConfig) (accepted : AcceptedModule config) (state : ExecutionState) (types : RootTypes)
      (next : TypingEnv) (typingAfter : Nat) (rootsAfter : RState),
      AcceptedFrame config accepted frame state types →
      typeStatements frame.typingFuel frame.typing statements frame.typingCounter = .ok (next, typingAfter) →
      rpStmts frame.source statements frame.rootCursor = .ok ((), rootsAfter) →
      AcceptedFrame config accepted { frame with
        typingFuel := 0
        typing := next
        typingCounter := typingAfter
        rootCursor := rootsAfter } state types := by
  induction checkedStatements with
  | nil frame =>
    intro config accepted state types next typingAfter rootsAfter source typed rooted
    cases nesting : frame.typingFuel with
    | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      rw [nesting] at typed
      change Except.ok (frame.typing, frame.typingCounter) = Except.ok (next, typingAfter) at typed
      change Except.ok ((), frame.rootCursor) = Except.ok ((), rootsAfter) at rooted
      cases typed
      cases rooted
      exact source.withTypingFuel 0
  | cons frame expression origin rest checkFuel ty roots typingAfter rootsAfter next statementAfter statementRootsAfter nesting form checked typed rooted tail ih =>
    intro config accepted state types finalTyping finalCounter finalRoots source allTyped allRooted
    obtain ⟨sameTyping, sameCounter, nextSource⟩ := checkedScalarExpression_statementAdvance config accepted frame state types source
      expression origin form checkFuel ty roots typingAfter rootsAfter checked next statementAfter statementRootsAfter typed rooted
    rw [nesting] at allTyped
    simp only [typeStatements, bind, StateT.bind, typed, Except.bind] at allTyped
    obtain ⟨middle, headRooted, tailRooted⟩ := rpStmts_cons allRooted
    have middleEq : middle = statementRootsAfter := (Prod.mk.inj (Except.ok.inj (headRooted.symm.trans rooted))).2
    subst middle
    have result := ih config accepted state types finalTyping finalCounter finalRoots nextSource allTyped tailRooted
    exact result

#print axioms checkedScalarStatements_finalFrame
#print axioms execStmts_checkedScalar_initializer
#print axioms scalarExpressionStatements_checked
#print axioms scalarExpressionStatements_effects_bounded
#print axioms typeStatement_expression_parts
end Goose.Proofs.ConstructionAcceptedExecution

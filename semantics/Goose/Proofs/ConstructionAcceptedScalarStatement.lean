import Goose.Proofs.ConstructionAcceptedBinaryComplete
import Goose.Proofs.ConstructionAcceptedByteSequence

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem execStmt_checkedScalarExpression_complete (expression : Expr) (origin : Goose.Core.OriginId)
    (form : AcceptedBinaryExpression expression) (fuel checkFuel : Nat) (config : EvalConfig)
    (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue (ordinaryOperandFrame frame checkFuel) expression ty roots typingAfter rootsAfter) :
    let outcome := execStmt fuel config frame.interpretation.environment (.expr expression origin) state
    Goose.Proofs.Exit.stepState outcome = state ∧
      (∀ flow after, outcome = .ok flow after → flow = .normal .unit ∧ after = state) ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types := by
  cases fuel with
  | zero => simp [execStmt, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
  | succ fuel =>
    have childSource := ordinaryOperandFrame_accepted accepted frame checkFuel state types source
    have result := evalValue_checked_binary_recursive form fuel config accepted (ordinaryOperandFrame frame checkFuel) state ambient types
      live regions pending world childSource ty roots typingAfter rootsAfter checked
    change Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment expression state) = state ∧ _ at result
    cases evaluated : evalValue fuel config frame.interpretation.environment expression state with
    | stop reason after | escape reason carriers after | jump reason kind after =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at result
      have same := result.1
      subst after
      simp only [execStmt, evaluated, bind, Goose.Proofs.Exit.stepState, reduceCtorEq, true_and]
      exact ⟨fun _ _ impossible => False.elim impossible, world, source⟩
    | ok value after =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at result
      have same := result.1
      subst after
      simp only [execStmt, evaluated, bind, pure, Goose.Proofs.Exit.stepState, ExecutionStep.ok.injEq, true_and]
      exact ⟨fun _ _ same => ⟨same.1.symm, same.2.symm⟩, world, source⟩

private theorem statement_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem checkedScalarExpression_statementAdvance (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes) (source : AcceptedFrame config accepted frame state types)
    (expression : Expr) (origin : Goose.Core.OriginId) (form : AcceptedBinaryExpression expression) (checkFuel : Nat)
    (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue (ordinaryOperandFrame frame checkFuel) expression ty roots typingAfter rootsAfter)
    (next : TypingEnv) (statementAfter : Nat) (statementRootsAfter : RState)
    (typed : typeStatement (checkFuel + 1) frame.typing (.expr expression origin) frame.typingCounter = .ok (next, statementAfter))
    (rooted : rpStmt frame.source (.expr expression origin) frame.rootCursor = .ok ((), statementRootsAfter)) :
    next = frame.typing ∧ statementAfter = frame.typingCounter ∧
      AcceptedFrame config accepted
        { frame with typingFuel := checkFuel + 1, typing := next, typingCounter := statementAfter, rootCursor := statementRootsAfter }
        state types := by
  have expressionTyping := checked.typing
  have expressionRoots := checked.provenance
  have cursor := checked_binary_recursive_cursor form (ordinaryOperandFrame frame checkFuel) ty roots typingAfter rootsAfter checked
  obtain ⟨otherRoots, rootedExpression⟩ := rpStmt_expression rooted
  have sameRoots := expressionRoots.symm.trans rootedExpression
  cases sameRoots
  simp only [typeStatement, bind, StateT.bind] at typed
  change (Except.bind (typeExpr checkFuel (ordinaryOperandFrame frame checkFuel).typing expression frame.typingCounter) _) = _ at typed
  simp only [ordinaryOperandFrame] at expressionTyping
  simp only [ordinaryOperandFrame] at typed
  rw [expressionTyping] at typed
  simp only [Except.bind] at typed
  obtain ⟨result, required, returned⟩ := statement_bind_success _ _ _ typed
  cases returned
  cases fixed : ty.nonfixed with
  | true =>
    simp only [List.all_cons, List.all_nil, Bool.and_true, fixed, Bool.not_true] at required
    change Except.error _ = Except.ok _ at required
    cases required
  | false =>
    simp only [List.all_cons, List.all_nil, Bool.and_true, fixed, Bool.not_false] at required
    change Except.ok ((), typingAfter) = Except.ok result at required
    cases required
    have counter : typingAfter = frame.typingCounter := cursor.1
    have nextVar : rootsAfter.nextVar = frame.rootCursor.nextVar := cursor.2
    subst typingAfter
    have initial := source.withTypingFuel (checkFuel + 1)
    refine ⟨rfl, rfl, ⟨⟨initial.compatible.module, initial.compatible.rootModule, initial.compatible.variables,
      initial.compatible.sourceVariables, initial.compatible.scopes, initial.compatible.globalCount,
      initial.compatible.globals, initial.compatible.initialized, ?_, initial.compatible.typingBound, ?_, initial.compatible.initializing,
      initial.compatible.currentScope, initial.compatible.origin⟩,
      initial.frontier, initial.scopeFrontier, ?_, initial.aliases, initial.locals, initial.localTypes, ?_, ?_,
      initial.futureGlobals, initial.direct, initial.contents⟩⟩
    · simpa only [nextVar] using initial.compatible.declarations
    · simpa only [nextVar] using initial.compatible.visible
    · simpa only [nextVar] using initial.initializingBefore
    · simpa only [nextVar] using initial.uninitializedLocals
    · simpa only [nextVar] using initial.uninitializedTypes

inductive CheckedScalarStatements : ConstructionSourceFrame → List Stmt → Prop
  | nil (frame : ConstructionSourceFrame) : CheckedScalarStatements frame []
  | cons (frame : ConstructionSourceFrame) (expression : Expr) (origin : Goose.Core.OriginId) (rest : List Stmt)
      (checkFuel : Nat) (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
      (next : TypingEnv) (statementAfter : Nat) (statementRootsAfter : RState)
      (nesting : frame.typingFuel = checkFuel + 2)
      (form : AcceptedBinaryExpression expression)
      (checked : CheckedValue (ordinaryOperandFrame frame checkFuel) expression ty roots typingAfter rootsAfter)
      (typed : typeStatement (checkFuel + 1) frame.typing (.expr expression origin) frame.typingCounter = .ok (next, statementAfter))
      (rooted : rpStmt frame.source (.expr expression origin) frame.rootCursor = .ok ((), statementRootsAfter))
      (tail : CheckedScalarStatements
        { frame with typingFuel := checkFuel + 1, typing := next, typingCounter := statementAfter, rootCursor := statementRootsAfter } rest) :
      CheckedScalarStatements frame (.expr expression origin :: rest)

theorem execStmts_checkedScalar_complete {frame : ConstructionSourceFrame} {statements : List Stmt}
    (checkedStatements : CheckedScalarStatements frame statements) :
    ∀ (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (state : ExecutionState)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
      (regions : List ReceivingRegion) (pending : List PendingCarrierFrame),
      AcceptedWorld config frame.initialized state ambient types live regions pending →
      AcceptedFrame config accepted frame state types → SourcePosition accepted frame (.statements statements) →
      let outcome := execStmts fuel config frame.interpretation.environment statements state
      Goose.Proofs.Exit.stepState outcome = state ∧
        (∀ flow after, outcome = .ok flow after → ∃ finalFrame,
          flow = .normal .unit ∧ after = state ∧ finalFrame.interpretation = frame.interpretation ∧
          finalFrame.initialized = frame.initialized ∧ AcceptedFrame config accepted finalFrame state types ∧
          SourcePosition accepted finalFrame (.statements [])) ∧
        AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
        AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types := by
  induction checkedStatements with
  | nil frame =>
    intro fuel config accepted state ambient types live regions pending world source position
    cases fuel with
    | zero => simp [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      simp only [execStmts, pure, Goose.Proofs.Exit.stepState, ExecutionStep.ok.injEq, true_and]
      refine ⟨?_, world, source⟩
      intro flow after same
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨frame, rfl, rfl, rfl, rfl, source, position⟩
  | cons frame expression origin rest checkFuel ty roots typingAfter rootsAfter next statementAfter statementRootsAfter nesting form checked typed rooted tail ih =>
    intro fuel config accepted state ambient types live regions pending world source position
    cases fuel with
    | zero => simp [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      let nextFrame := { frame with typingFuel := checkFuel + 1, typing := next, typingCounter := statementAfter, rootCursor := statementRootsAfter }
      obtain ⟨sameTyping, sameCounter, nextSource⟩ := checkedScalarExpression_statementAdvance config accepted frame state types source
        expression origin form checkFuel ty roots typingAfter rootsAfter checked next statementAfter statementRootsAfter typed rooted
      have nextPosition := position.statements_tail accepted frame (.expr expression origin) rest (checkFuel + 1) next statementAfter
        statementRootsAfter nesting typed rooted
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
        have result := head.2.1 flow after executed
        obtain ⟨sameFlow, sameAfter⟩ := result
        subst flow after
        have nextWorld : AcceptedWorld config nextFrame.initialized state ambient types live regions pending := world
        have final := ih fuel config accepted state ambient types live regions pending nextWorld nextSource nextPosition
        change Goose.Proofs.Exit.stepState (execStmts fuel config frame.interpretation.environment rest state) = state ∧
          (∀ flow after, execStmts fuel config frame.interpretation.environment rest state = .ok flow after → _) ∧ _ at final
        simp only [execStmts, bind, executed]
        refine ⟨final.1, ?_, by simpa only [final.1] using world, by simpa only [final.1] using source⟩
        intro flow after completed
        obtain ⟨last, sameFlow, sameAfter, interpretation, initialized, lastSource, lastPosition⟩ := final.2.1 flow after completed
        exact ⟨last, sameFlow, sameAfter, interpretation, initialized, lastSource, lastPosition⟩

#print axioms execStmts_checkedScalar_complete
#print axioms checkedScalarExpression_statementAdvance
#print axioms execStmt_checkedScalarExpression_complete
end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionAcceptedGlobalAssignBlockValue
import Goose.Proofs.ConstructionAcceptedScalarAssignCursors
import Goose.Proofs.ConstructionAcceptedBlockTailChecks

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem statefulBlock_expression_cursors (checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
    (scope id origin blockOrigin : Nat) (expression : Expr) (intTy : Goose.Core.IntTy) (literal : Int)
    (form : AcceptedBinaryExpression expression)
    (source : AcceptedFrame config accepted frame state types)
    (initialized : frame.initialized = config.module.globals.size)
    (fresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ scope)
    (absent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (position : SourcePosition accepted frame (.expression (.blockE
      ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin)))
    (nesting : frame.typingFuel = checkFuel + 4)
    (resultTypes : List Ty) (typingAfter : Nat) (roots : List RootRef) (rootsAfter : RState)
    (typed : typeExpr frame.typingFuel frame.typing (.blockE
      ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) frame.typingCounter = .ok (resultTypes, typingAfter))
    (rooted : rpExpr frame.source (.blockE
      ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) frame.rootCursor = .ok (roots, rootsAfter)) :
    typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar := by
  rw [nesting] at typed
  obtain ⟨expected, query, blockTyped, sameTypes⟩ := typeExpr_blockE_tail (checkFuel + 3) frame.typing scope
    [.assign (.global id) expression origin] (.lit intTy literal) blockOrigin frame.typingCounter typingAfter resultTypes typed
  obtain ⟨rootStart, rootEnd, bodyRootAfter, bodyRooted, restored⟩ := rpExpr_blockE_body frame.source scope
    [.assign (.global id) expression origin] (some (.lit intTy literal)) blockOrigin frame.rootCursor rootsAfter roots rooted
  let bodyFrame := valueBlockExpressionFrame frame scope (checkFuel + 3) expected
  have bodyPosition : SourcePosition accepted bodyFrame (.block ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩) := by
    exact .child position (.valueBlockExpression frame scope (checkFuel + 3) blockOrigin _ _ expected (by simpa [Nat.add_assoc] using nesting) query)
      ⟨resultTypes, typingAfter, (roots, (rootStart, rootEnd)), bodyRootAfter, blockTyped, bodyRooted⟩
  let child := unusedChildScopeFrame bodyFrame scope state.nextScope (checkFuel + 2)
  have bodySource := source.valueBlockExpression scope (checkFuel + 3) expected
  have childSource : AcceptedFrame config accepted child { state with nextScope := state.nextScope + 1 } types := by
    apply bodySource.enterScope_withoutDeclarations scope (checkFuel + 2)
    · simpa [bodyFrame, valueBlockExpressionFrame] using fresh
    · simpa [bodyFrame, valueBlockExpressionFrame] using absent
  have childPosition : SourcePosition accepted child (.statements [.assign (.global id) expression origin]) := by
    have statementPosition := bodyPosition.block_statements accepted bodyFrame scope (checkFuel + 2)
      [.assign (.global id) expression origin] (some (.lit intTy literal)) rfl
    have actual := SourcePosition.instantiate statementPosition (frame.interpretation.enterScope scope state.nextScope) frame.initialized
    simpa [child, unusedChildScopeFrame, blockStatementsFrame, bodyFrame, valueBlockExpressionFrame] using actual
  have headPosition := childPosition.statements_head accepted child (.assign (.global id) expression origin) [] (checkFuel + 1) rfl
  obtain ⟨next, headTypingAfter, headRootsAfter, headTyped, headRooted⟩ := headPosition.checked accepted _ _
  have cursors := scalarAssign_statement_cursors checkFuel config accepted child { state with nextScope := state.nextScope + 1 } types
    (.global id) expression origin form next headTypingAfter headRootsAfter childSource initialized (Or.inr ⟨id, rfl⟩) headTyped headRooted
  obtain ⟨blockNext, blockMiddle, rootMiddle, bodyTypes, bodyAfter, bodyRoots, bodyRootsAfter,
    bodyTyped, statementsTyped, statementsRooted, tailTyped, tailRooted⟩ :=
      bodyPosition.blockTail_checks accepted bodyFrame scope (checkFuel + 2)
        [.assign (.global id) expression origin] (.lit intTy literal) rfl
  simp only [typeStatements, bind, StateT.bind] at statementsTyped
  simp only [child, unusedChildScopeFrame, bodyFrame, valueBlockExpressionFrame] at headTyped headRooted cursors
  simp only [bodyFrame, valueBlockExpressionFrame] at statementsTyped
  rw [headTyped] at statementsTyped
  have stateTyping : blockMiddle = frame.typingCounter := by
    simp only [Except.bind, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at statementsTyped
    exact statementsTyped.2.symm.trans cursors.2.1
  have statementRoot := rpStmts_cons statementsRooted
  obtain ⟨rootAfter, firstRoot, restRoot⟩ := statementRoot
  simp only [rpStmts, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, true_and] at restRoot
  subst rootAfter
  simp only [bodyFrame, valueBlockExpressionFrame] at firstRoot
  rw [headRooted] at firstRoot
  cases firstRoot
  have stateRoot : headRootsAfter.nextVar = frame.rootCursor.nextVar := by
    simpa [bodyFrame, valueBlockExpressionFrame] using cursors.2.2
  have typedEqual : (bodyTypes, bodyAfter) = (resultTypes, typingAfter) := by
    simpa [bodyFrame, valueBlockExpressionFrame] using bodyTyped.symm.trans blockTyped
  have tailCounter : bodyAfter = blockMiddle := by
    cases checkFuel <;> simp [typeExpr, pure, StateT.pure, Except.pure] at tailTyped <;> exact tailTyped.2.symm
  have typingEq : typingAfter = frame.typingCounter := by
    have equalAfter := congrArg Prod.snd typedEqual
    simpa [stateTyping] using equalAfter.symm.trans tailCounter
  obtain ⟨_, actualMiddle, actualRoots, actualStatements, actualTail, actualResult⟩ := rpBlockValue_body bodyRooted
  simp only [List.length_nil, Nat.add_zero] at actualStatements
  have rootEq : actualMiddle = headRootsAfter := by
    simp only [bodyFrame, valueBlockExpressionFrame] at statementsRooted
    rw [statementsRooted] at actualStatements
    exact (congrArg Prod.snd (Except.ok.inj actualStatements)).symm
  subst actualMiddle
  simp [rpExpr, pure, StateT.pure, Except.pure] at actualTail
  have finalRoot : bodyRootAfter = headRootsAfter := actualTail.2.symm
  constructor
  · exact typingEq
  · rw [restored]
    simpa [finalRoot] using stateRoot

#print axioms statefulBlock_expression_cursors
end Goose.Proofs.ConstructionAcceptedExecution

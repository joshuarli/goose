import Goose.Proofs.ConstructionAcceptedNestedBlockValue
import Goose.Proofs.ConstructionAcceptedStatefulBlockCursors

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem nestedBlock_expression_cursors (sourceFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
    (outerScope innerScope id origin innerOrigin outerOrigin : Nat) (expression : Expr) (intTy : Goose.Core.IntTy) (literal : Int)
    (form : AcceptedBinaryExpression expression) (source : AcceptedFrame config accepted frame state types)
    (initialized : frame.initialized = config.module.globals.size)
    (outerFresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ outerScope)
    (innerFresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ innerScope)
    (different : innerScope ≠ outerScope)
    (outerAbsent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ outerScope)
    (innerAbsent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ innerScope)
    (position : SourcePosition accepted frame (.expression (.blockE ⟨outerScope, [], some (.blockE
      ⟨innerScope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ innerOrigin)⟩ outerOrigin)))
    (nesting : frame.typingFuel = sourceFuel + 2)
    (resultTypes : List Ty) (typingAfter : Nat) (roots : List RootRef) (rootsAfter : RState)
    (typed : typeExpr frame.typingFuel frame.typing (.blockE ⟨outerScope, [], some (.blockE
      ⟨innerScope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ innerOrigin)⟩ outerOrigin) frame.typingCounter = .ok (resultTypes, typingAfter))
    (rooted : rpExpr frame.source (.blockE ⟨outerScope, [], some (.blockE
      ⟨innerScope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ innerOrigin)⟩ outerOrigin) frame.rootCursor = .ok (roots, rootsAfter)) :
    typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar ∧ resultTypes = [.int intTy] := by
  let inner : Expr := .blockE ⟨innerScope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ innerOrigin
  rw [nesting] at typed
  obtain ⟨expected, query, blockTyped, sameTypes⟩ := typeExpr_blockE_tail (sourceFuel + 1) frame.typing outerScope [] inner
    outerOrigin frame.typingCounter typingAfter resultTypes typed
  obtain ⟨rootStart, rootEnd, bodyRootAfter, bodyRooted, restored⟩ := rpExpr_blockE_body frame.source outerScope [] (some inner)
    outerOrigin frame.rootCursor rootsAfter roots rooted
  let bodyFrame := valueBlockExpressionFrame frame outerScope (sourceFuel + 1) expected
  have bodyPosition : SourcePosition accepted bodyFrame (.block ⟨outerScope, [], some inner⟩) :=
    .child position (.valueBlockExpression frame outerScope (sourceFuel + 1) outerOrigin [] inner expected (by simpa [Nat.add_assoc] using nesting) query)
      ⟨resultTypes, typingAfter, (roots, (rootStart, rootEnd)), bodyRootAfter, blockTyped, bodyRooted⟩
  have bodySource := source.valueBlockExpression outerScope (sourceFuel + 1) expected
  obtain ⟨next, middle, rootMiddle, bodyTypes, bodyAfter, bodyRoots, bodyRootsAfter,
    bodyTyped, statementsTyped, statementsRooted, tailTyped, tailRooted⟩ :=
      bodyPosition.blockTail_checks accepted bodyFrame outerScope sourceFuel [] inner rfl
  cases sourceFuel with
  | zero => change Except.error _ = Except.ok _ at statementsTyped; cases statementsTyped
  | succ sourceFuel =>
    have typedEq : next = { bodyFrame.typing with scope := outerScope } ∧ middle = bodyFrame.typingCounter := by
      simpa [typeStatements, pure, StateT.pure, Except.pure] using statementsTyped.symm
    have rootEq : rootMiddle = bodyFrame.rootCursor := by simpa [rpStmts, pure, bind, StateT.pure, Except.pure] using statementsRooted.symm
    obtain ⟨rfl, rfl⟩ := typedEq
    subst rootMiddle
    let child := unusedChildScopeFrame bodyFrame outerScope state.nextScope (sourceFuel + 1)
    have childSource : AcceptedFrame config accepted child { state with nextScope := state.nextScope + 1 } types := by
      apply bodySource.enterScope_withoutDeclarations outerScope (sourceFuel + 1)
      · simpa [bodyFrame, valueBlockExpressionFrame] using outerFresh
      · simpa [bodyFrame, valueBlockExpressionFrame] using outerAbsent
    have tailPosition : SourcePosition accepted
        { bodyFrame with typingFuel := sourceFuel + 1, typing := { bodyFrame.typing with scope := outerScope }, source := { bodyFrame.source with scopes := outerScope :: bodyFrame.source.scopes } } (.expression inner) :=
      .child bodyPosition (.blockTail bodyFrame outerScope (sourceFuel + 1) [] inner _ _ _ rfl statementsTyped statementsRooted)
        ⟨bodyTypes, bodyAfter, bodyRoots, bodyRootsAfter, tailTyped, tailRooted⟩
    have instantiated := SourcePosition.instantiate tailPosition (bodyFrame.interpretation.enterScope outerScope state.nextScope) bodyFrame.initialized
    have childPosition : SourcePosition accepted child (.expression inner) := by
      simpa [child, unusedChildScopeFrame, typeStatements, pure, StateT.pure, Except.pure, rpStmts, bind] using instantiated
    have childTyped : typeExpr child.typingFuel child.typing inner child.typingCounter = .ok (bodyTypes, bodyAfter) := by
      simpa [child, unusedChildScopeFrame] using tailTyped
    have childRooted : rpExpr child.source inner child.rootCursor = .ok (bodyRoots, bodyRootsAfter) := by
      simpa [child, unusedChildScopeFrame] using tailRooted
    have enough := typeExpr_statefulBlock_fuel child.typingFuel child.typing innerScope id origin innerOrigin expression intTy literal
      child.typingCounter bodyAfter bodyTypes childTyped
    let checkFuel := child.typingFuel - 4
    have innerNesting : child.typingFuel = checkFuel + 4 := by dsimp [checkFuel]; omega
    have fresh : ∀ entry ∈ child.interpretation.environment.scopes, entry.1 ≠ innerScope := by
      intro entry member
      simp only [child, unusedChildScopeFrame, RootInterpretation.enterScope, List.mem_cons, bodyFrame, valueBlockExpressionFrame] at member
      rcases member with equal | member
      · subst entry; exact different.symm
      · exact innerFresh entry member
    have absent : ∀ descriptor ∈ child.interpretation.environment.vars.toList, descriptor.scope ≠ innerScope := by
      simpa [child, unusedChildScopeFrame, bodyFrame, valueBlockExpressionFrame, RootInterpretation.enterScope] using innerAbsent
    have cursors := statefulBlock_expression_cursors checkFuel config accepted child _ types innerScope id origin innerOrigin expression intTy literal
      form childSource initialized fresh absent childPosition innerNesting bodyTypes bodyAfter bodyRoots bodyRootsAfter childTyped childRooted
    have typedEqual : (bodyTypes, bodyAfter) = (resultTypes, typingAfter) := by
      simpa [bodyFrame, valueBlockExpressionFrame] using bodyTyped.symm.trans blockTyped
    have typingEq : typingAfter = frame.typingCounter := by
      have afterEq := congrArg Prod.snd typedEqual
      simpa [child, unusedChildScopeFrame, bodyFrame, valueBlockExpressionFrame] using afterEq.symm.trans cursors.1
    obtain ⟨_, actualMiddle, actualRoots, actualStatements, actualTail, actualResult⟩ := rpBlockValue_body bodyRooted
    simp only [List.length_nil, Nat.add_zero] at actualStatements
    have actualMiddleEq : actualMiddle = bodyFrame.rootCursor := by
      simpa [bodyFrame, valueBlockExpressionFrame, rpStmts, pure, bind, StateT.pure, Except.pure] using actualStatements.symm
    subst actualMiddle
    have finalRoot : bodyRootAfter = bodyRootsAfter := by
      change rpExpr { bodyFrame.source with scopes := outerScope :: bodyFrame.source.scopes } inner bodyFrame.rootCursor = .ok (actualRoots, bodyRootAfter) at actualTail
      rw [tailRooted] at actualTail
      exact (congrArg Prod.snd (Except.ok.inj actualTail)).symm
    have innerTypes := typeExpr_integerTail_result (checkFuel + 1) child.typing innerScope [.assign (.global id) expression origin]
      intTy literal innerOrigin child.typingCounter bodyAfter bodyTypes (by simpa [inner, innerNesting, Nat.add_assoc] using childTyped)
    have resultEq : resultTypes = [.int intTy] := (congrArg Prod.fst typedEqual).symm.trans innerTypes
    refine ⟨typingEq, ?_, resultEq⟩
    rw [restored, finalRoot]
    simpa [child, unusedChildScopeFrame, bodyFrame, valueBlockExpressionFrame] using cursors.2

#print axioms nestedBlock_expression_cursors
end Goose.Proofs.ConstructionAcceptedExecution

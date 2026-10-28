import Goose.Proofs.ConstructionAcceptedNestedBlockPosition
import Goose.Proofs.ConstructionAcceptedGlobalAssignBlockProduce
import Goose.Proofs.ConstructionAcceptedStatefulCallFuel

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

theorem nestedTail_globalAssign_safe (fuel sourceFuel : Nat)
    (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (outerScope innerScope id origin blockOrigin : Nat) (expression : Expr) (intTy : Goose.Core.IntTy) (literal : Int)
    (form : AcceptedBinaryExpression expression)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (initialized : frame.initialized = config.module.globals.size)
    (outerFresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ outerScope)
    (innerFresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ innerScope)
    (different : innerScope ≠ outerScope)
    (outerAbsent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ outerScope)
    (innerAbsent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ innerScope)
    (scalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool)
    (position : SourcePosition accepted frame (.block ⟨outerScope, [], some (.blockE
      ⟨innerScope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin)⟩))
    (nesting : frame.typingFuel = sourceFuel + 1) :
    let scopeState := ownershipResultScopeState frame.interpretation.environment outerScope state
    let child := unusedChildScopeFrame frame outerScope state.nextScope sourceFuel
    let step := evalProduce fuel config child.interpretation.environment [.register (.int intTy)]
      (.blockE ⟨innerScope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) scopeState
    RegisterBreakActionOutcome config accepted child ambient types live regions pending step ∧
      match step with | .ok carriers _ => carriers = [.register (.int intTy literal)] | _ => True := by
  let scopeState := ownershipResultScopeState frame.interpretation.environment outerScope state
  let child := unusedChildScopeFrame frame outerScope state.nextScope sourceFuel
  have scopedWorld : AcceptedWorld config child.initialized scopeState ambient types live regions pending :=
    acceptedWorld_resultScope config frame.initialized state ambient types live regions pending frame.interpretation.environment outerScope world
  have childSource : AcceptedFrame config accepted child scopeState types := by
    have entered := source.enterScope_withoutDeclarations outerScope sourceFuel outerFresh outerAbsent
    have actual := entered.withActivations (({ state with nextScope := state.nextScope + 1 }).activations.map fun (current : RuntimeActivation) =>
      if current.act == frame.interpretation.environment.act then
        { current with scopes := (outerScope, state.nextScope) :: frame.interpretation.environment.scopes } else current)
    simpa [scopeState, ownershipResultScopeState, child] using actual
  obtain ⟨next, typingMiddle, rootMiddle, typed, rooted, tailPosition⟩ := position.blockTail accepted frame outerScope sourceFuel [] _ nesting
  cases sourceFuel with
  | zero => change Except.error _ = Except.ok _ at typed; cases typed
  | succ sourceFuel =>
    have typedEq : next = { frame.typing with scope := outerScope } ∧ typingMiddle = frame.typingCounter := by
      simpa [typeStatements, pure, StateT.pure, Except.pure] using typed.symm
    have rootEq : rootMiddle = frame.rootCursor := by simpa [rpStmts, pure, bind, StateT.pure, Except.pure] using rooted.symm
    obtain ⟨rfl, rfl⟩ := typedEq
    subst rootMiddle
    have instantiated := SourcePosition.instantiate tailPosition (frame.interpretation.enterScope outerScope state.nextScope) frame.initialized
    have childPosition : SourcePosition accepted child (.expression (.blockE
        ⟨innerScope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin)) := by
      simpa [child, unusedChildScopeFrame] using instantiated
    obtain ⟨innerTypes, typingAfter, roots, rootsAfter, innerTyped, innerRooted⟩ := childPosition.checked accepted child _
    have enough := typeExpr_statefulBlock_fuel child.typingFuel child.typing innerScope id origin blockOrigin expression intTy literal
      child.typingCounter typingAfter innerTypes innerTyped
    let checkFuel := child.typingFuel - 4
    have innerNesting : child.typingFuel = checkFuel + 4 := by dsimp [checkFuel]; omega
    obtain ⟨expected, bodyPosition⟩ := childPosition.valueBlockExpression accepted child innerScope (checkFuel + 3) blockOrigin
      [.assign (.global id) expression origin] (.lit intTy literal) (by simpa [Nat.add_assoc] using innerNesting)
    let bodyFrame := valueBlockExpressionFrame child innerScope (checkFuel + 3) expected
    have bodySource := childSource.valueBlockExpression innerScope (checkFuel + 3) expected
    have fresh : ∀ entry ∈ child.interpretation.environment.scopes, entry.1 ≠ innerScope := by
      intro entry member
      simp only [child, unusedChildScopeFrame, RootInterpretation.enterScope, List.mem_cons] at member
      rcases member with equal | member
      · subst entry; exact different.symm
      · exact innerFresh entry member
    have absent : ∀ descriptor ∈ child.interpretation.environment.vars.toList, descriptor.scope ≠ innerScope := by
      simpa [child, unusedChildScopeFrame, RootInterpretation.enterScope] using innerAbsent
    have innerSafe := evalProduce_globalAssign_integerTail_world fuel checkFuel config accepted bodyFrame scopeState ambient types live regions pending
      innerScope id expression origin blockOrigin intTy literal form scopedWorld bodySource initialized fresh absent bodyPosition rfl scalar
    cases produced : evalProduce fuel config child.interpretation.environment [.register (.int intTy)]
        (.blockE ⟨innerScope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) scopeState with
    | escape address carriers after | jump target kind after =>
      simp [bodyFrame, valueBlockExpressionFrame, produced, RegisterBreakActionOutcome] at innerSafe
    | stop reason after =>
      simp only [bodyFrame, valueBlockExpressionFrame, produced, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] at innerSafe
      have afterSource := childSource.leaveValueBlockExpression innerScope (checkFuel + 3) expected innerSafe.1.2.1
      simpa [child, scopeState, produced, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] using
        And.intro (And.intro innerSafe.1.1 (And.intro afterSource True.intro)) True.intro
    | ok carriers after =>
      simp only [bodyFrame, valueBlockExpressionFrame, produced, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] at innerSafe
      have afterSource := childSource.leaveValueBlockExpression innerScope (checkFuel + 3) expected innerSafe.1.2.1
      simpa [child, scopeState, produced, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] using
        And.intro (And.intro innerSafe.1.1 (And.intro afterSource True.intro)) innerSafe.2

#print axioms nestedTail_globalAssign_safe
end Goose.Proofs.ConstructionAcceptedExecution

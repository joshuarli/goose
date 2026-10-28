import Goose.Proofs.ConstructionAcceptedGlobalAssignFrame
import Goose.Proofs.ConstructionAcceptedScopeWorld
import Goose.Proofs.ConstructionAcceptedLocalFreshness

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem AcceptedFrame.releaseEmptyScope {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types)
    (emptyFrame : frame.interpretation.environment.vars = #[])
    (environment : RuntimeActivation) (emptyScope : environment.vars = #[]) (scope scopeInst : Nat) :
    AcceptedFrame config accepted frame (releaseScopeState environment scope scopeInst state) types := by
  have noVisible : frame.typing.visible = [] := by
    have emptyTypes : frame.typing.variables = #[] := source.compatible.variables.symm.trans emptyFrame
    have zeroCounter : frame.typingCounter = 0 := by
      have bound := source.compatible.typingBound
      simp only [emptyTypes, Array.size_empty] at bound
      omega
    have zeroRoots : frame.rootCursor.nextVar = 0 := by
      have bound := source.compatible.declarations
      omega
    cases visible : frame.typing.visible with
    | nil => rfl
    | cons id rest =>
      have bound := source.compatible.visible id (by simp [visible])
      rw [zeroRoots] at bound
      exact (Nat.not_lt_zero id bound).elim
  refine ⟨source.compatible, ?_, ?_, source.initializingBefore, source.aliases, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [releaseScopeState] using source.frontier
  · simpa [releaseScopeState] using source.scopeFrontier
  · simp [LocalRepresentations, noVisible]
  · simp [noVisible]
  · intro id condition root resolved
    simp [rootOf, emptyFrame, fault, EvalM.stop] at resolved
  · intro id condition root resolved
    simp [rootOf, emptyFrame, fault, EvalM.stop] at resolved
  · intro id future inside
    simpa [releaseScopeState, emptyScope] using source.futureGlobals id future inside
  · simp [LocalRootCorrespondence, noVisible]
  · simp [ContentRootCorrespondence, noVisible]

def emptyChildScopeFrame (frame : ConstructionSourceFrame) (scope scopeInst fuel : Nat) : ConstructionSourceFrame :=
  { frame with
    typing := { frame.typing with scope := scope }
    source := { frame.source with scopes := scope :: frame.source.scopes }
    interpretation := frame.interpretation.enterScope scope scopeInst
    typingFuel := fuel }

theorem AcceptedFrame.enterEmptyScope {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types)
    (emptyFrame : frame.interpretation.environment.vars = #[]) (scope fuel : Nat) :
    AcceptedFrame config accepted (emptyChildScopeFrame frame scope state.nextScope fuel)
      { state with nextScope := state.nextScope + 1 } types := by
  let next := emptyChildScopeFrame frame scope state.nextScope fuel
  let after := { state with nextScope := state.nextScope + 1 }
  have emptyTypes : frame.typing.variables = #[] := source.compatible.variables.symm.trans emptyFrame
  have noVisible : frame.typing.visible = [] := by
    have zeroCounter : frame.typingCounter = 0 := by
      have bound := source.compatible.typingBound
      simp only [emptyTypes, Array.size_empty] at bound
      omega
    have zeroRoots : frame.rootCursor.nextVar = 0 := by
      have bound := source.compatible.declarations
      omega
    cases visible : frame.typing.visible with
    | nil => rfl
    | cons id rest =>
      have bound := source.compatible.visible id (by simp [visible])
      rw [zeroRoots] at bound
      exact (Nat.not_lt_zero id bound).elim
  have compatible : SourceFrameCompatible accepted next := by
    refine ⟨source.compatible.module, source.compatible.rootModule, ?_, source.compatible.sourceVariables, ?_,
      source.compatible.globalCount, source.compatible.globals, source.compatible.initialized,
      source.compatible.declarations, source.compatible.typingBound, source.compatible.visible,
      source.compatible.initializing, ?_, ?_⟩
    · simpa [next, emptyChildScopeFrame, RootInterpretation.enterScope] using source.compatible.variables
    · simp [next, emptyChildScopeFrame, RootInterpretation.enterScope, source.compatible.scopes]
    · intro actual rest same
      simpa [next, emptyChildScopeFrame] using (List.cons.inj same).1
    · have origin := source.compatible.origin
      cases phase : frame.phase <;> simpa [SourceOrigin, next, emptyChildScopeFrame, RootInterpretation.enterScope, phase] using origin
  have frontier : RootFrontier next.interpretation after.nextAct :=
    rootFrontier_enterScope frame.interpretation scope state.nextScope state.nextAct source.frontier
  have aliases : AliasComplete next.interpretation next.source.aliases :=
    aliasComplete_enterScope frame.interpretation frame.source.aliases scope state.nextScope state.nextAct source.frontier source.aliases
  refine ⟨compatible, frontier, ?_, source.initializingBefore, aliases, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [next, emptyChildScopeFrame, RootInterpretation.enterScope, after] using source.enterScope_frontier scope
  · simp [emptyChildScopeFrame, LocalRepresentations, noVisible]
  · simp [emptyChildScopeFrame, noVisible]
  · intro id condition root resolved
    simp [emptyChildScopeFrame, RootInterpretation.enterScope, rootOf, emptyFrame, fault, EvalM.stop] at resolved
  · intro id condition root resolved
    simp [emptyChildScopeFrame, RootInterpretation.enterScope, rootOf, emptyFrame, fault, EvalM.stop] at resolved
  · exact source.futureGlobals
  · simp [emptyChildScopeFrame, LocalRootCorrespondence, noVisible]
  · simp [emptyChildScopeFrame, ContentRootCorrespondence, noVisible]

theorem AcceptedFrame.leaveEmptyChild {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {before after : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame before types)
    (emptyFrame : frame.interpretation.environment.vars = #[]) (scope scopeInst fuel : Nat)
    (child : AcceptedFrame config accepted (emptyChildScopeFrame frame scope scopeInst fuel) after types) :
    AcceptedFrame config accepted frame after types := by
  have emptyTypes : frame.typing.variables = #[] := source.compatible.variables.symm.trans emptyFrame
  have noVisible : frame.typing.visible = [] := by
    have zeroCounter : frame.typingCounter = 0 := by
      have bound := source.compatible.typingBound
      simp only [emptyTypes, Array.size_empty] at bound
      omega
    have zeroRoots : frame.rootCursor.nextVar = 0 := by
      have bound := source.compatible.declarations
      omega
    cases visible : frame.typing.visible with
    | nil => rfl
    | cons id rest =>
      have bound := source.compatible.visible id (by simp [visible])
      rw [zeroRoots] at bound
      exact (Nat.not_lt_zero id bound).elim
  refine ⟨source.compatible, ?_, ?_, source.initializingBefore, source.aliases, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [RootFrontier, emptyChildScopeFrame, RootInterpretation.enterScope] using child.frontier
  · intro entry member
    apply child.scopeFrontier entry
    simp [emptyChildScopeFrame, RootInterpretation.enterScope, member]
  · simp [LocalRepresentations, noVisible]
  · simp [noVisible]
  · intro id condition root resolved
    simp [rootOf, emptyFrame, fault, EvalM.stop] at resolved
  · intro id condition root resolved
    simp [rootOf, emptyFrame, fault, EvalM.stop] at resolved
  · exact child.futureGlobals
  · simp [LocalRootCorrespondence, noVisible]
  · simp [ContentRootCorrespondence, noVisible]

#print axioms AcceptedFrame.leaveEmptyChild
#print axioms AcceptedFrame.enterEmptyScope
#print axioms AcceptedFrame.releaseEmptyScope
end Goose.Proofs.ConstructionAcceptedExecution

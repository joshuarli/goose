import Goose.Proofs.ConstructionAcceptedScopeWorld
import Goose.Proofs.ConstructionAcceptedCallerContents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

theorem runtimeScopeRoots_empty_of_noDeclarations (environment : RuntimeActivation) (scope scopeInst : Nat)
    (absent : ∀ descriptor ∈ environment.vars.toList, descriptor.scope ≠ scope) :
    Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst = [] := by
  simp only [Goose.Proofs.Exit.runtimeScopeRoots, List.filterMap_eq_nil_iff]
  intro pair member
  rcases pair with ⟨descriptor, index⟩
  have indexed := List.mem_zipIdx member
  have inVariables : descriptor ∈ environment.vars.toList := by
    rw [indexed.2.2]
    exact List.getElem_mem (by simpa using indexed.2.1)
  have different := absent descriptor inVariables
  simp [different]

theorem rootOf_enterScope_withoutDeclarations (interpretation : RootInterpretation) (scope scopeInst id : Nat)
    (absent : ∀ descriptor ∈ interpretation.environment.vars.toList, descriptor.scope ≠ scope) :
    rootOf (interpretation.enterScope scope scopeInst).environment id = rootOf interpretation.environment id := by
  funext state
  cases declared : interpretation.environment.vars[id]? with
  | none => simp [RootInterpretation.enterScope, rootOf, declared]
  | some descriptor =>
    have member : descriptor ∈ interpretation.environment.vars.toList :=
      Array.mem_toList_iff.mpr (Array.mem_of_getElem? declared)
    have different : (scope == descriptor.scope) = false := beq_eq_false_iff_ne.mpr (absent descriptor member).symm
    simp [RootInterpretation.enterScope, rootOf, declared, different]

theorem AcceptedWorld.releaseScope_withoutDeclarations (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (environment : RuntimeActivation) (scope scopeInst : Nat)
    (absent : ∀ descriptor ∈ environment.vars.toList, descriptor.scope ≠ scope)
    (world : AcceptedWorld config initialized state ambient types live regions pending) :
    AcceptedWorld config initialized (releaseScopeState environment scope scopeInst state) ambient types live regions pending := by
  have result := world.releaseScope config initialized state ambient types live regions pending environment scope scopeInst
  have roots := runtimeScopeRoots_empty_of_noDeclarations environment scope scopeInst absent
  have same : (fun root => live root ∧ (Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst).contains root = false) = live := by
    funext root
    simp [roots]
  rwa [same] at result

theorem AcceptedFrame.releaseScope_withoutDeclarations {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types)
    (environment : RuntimeActivation) (scope scopeInst : Nat)
    (absent : ∀ descriptor ∈ environment.vars.toList, descriptor.scope ≠ scope) :
    AcceptedFrame config accepted frame (releaseScopeState environment scope scopeInst state) types := by
  have roots := runtimeScopeRoots_empty_of_noDeclarations environment scope scopeInst absent
  apply source.afterFreshActivation
  · simp [releaseScopeState]
  · simp [releaseScopeState]
  · intro root outside
    apply Goose.Proofs.ExitExecution.releaseScopeState_root_lookup
    simp [roots]
  · intro root outside
    apply releaseScopeState_ordinal_lookup
    simp [roots]
  · intro root outside
    rfl

theorem AcceptedFrame.withActivations {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (activations : List RuntimeActivation) :
    AcceptedFrame config accepted frame { state with activations := activations } types := by
  apply source.afterFreshActivation <;> simp

#print axioms AcceptedFrame.withActivations

def unusedChildScopeFrame (frame : ConstructionSourceFrame) (scope scopeInst fuel : Nat) : ConstructionSourceFrame :=
  { frame with
    typing := { frame.typing with scope := scope }
    source := { frame.source with scopes := scope :: frame.source.scopes }
    interpretation := frame.interpretation.enterScope scope scopeInst
    typingFuel := fuel }

theorem AcceptedFrame.enterScope_withoutDeclarations {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (scope fuel : Nat)
    (fresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ scope)
    (absent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ scope) :
    AcceptedFrame config accepted (unusedChildScopeFrame frame scope state.nextScope fuel)
      { state with nextScope := state.nextScope + 1 } types := by
  let after := { state with nextScope := state.nextScope + 1 }
  let next := unusedChildScopeFrame frame scope state.nextScope fuel
  have bumped : AcceptedFrame config accepted frame after types := source.afterFreshActivation
    (by simp [after]) (by simp [after]) (by intros; rfl) (by intros; rfl) (by intros; rfl)
  have compatible : SourceFrameCompatible accepted next := by
    refine ⟨source.compatible.module, source.compatible.rootModule, ?_, source.compatible.sourceVariables, ?_,
      source.compatible.globalCount, source.compatible.globals, source.compatible.initialized,
      source.compatible.declarations, source.compatible.typingBound, source.compatible.visible,
      source.compatible.initializing, ?_, ?_⟩
    · simpa [next, unusedChildScopeFrame, RootInterpretation.enterScope] using source.compatible.variables
    · simp [next, unusedChildScopeFrame, RootInterpretation.enterScope, source.compatible.scopes]
    · intro actual rest same
      simpa [next, unusedChildScopeFrame] using (List.cons.inj same).1
    · have origin := source.compatible.origin
      cases phase : frame.phase <;> simpa [SourceOrigin, next, unusedChildScopeFrame, RootInterpretation.enterScope, phase] using origin
  have roots := rootOf_enterScope_withoutDeclarations frame.interpretation scope state.nextScope
  have active : ∀ id ∈ frame.typing.visible, ∃ root, rootOf frame.interpretation.environment id after = .ok root after := by
    intro id member
    obtain ⟨descriptor, root, value, _, resolved, _, _⟩ := bumped.locals id member
    exact ⟨root, resolved⟩
  refine ⟨compatible, rootFrontier_enterScope frame.interpretation scope state.nextScope after.nextAct bumped.frontier,
    ?_, bumped.initializingBefore, aliasComplete_enterScope frame.interpretation frame.source.aliases scope state.nextScope after.nextAct bumped.frontier bumped.aliases,
    ?_, ?_, ?_, ?_, bumped.futureGlobals, ?_, ?_⟩
  · intro entry member
    simp only [next, unusedChildScopeFrame, RootInterpretation.enterScope, List.mem_cons] at member
    rcases member with equal | old
    · subst entry
      exact Nat.lt_succ_self _
    · exact bumped.scopeFrontier entry old
  · intro id member
    obtain ⟨descriptor, root, value, declared, resolved, found, represented⟩ := bumped.locals id member
    exact ⟨descriptor, root, value, declared, by simpa [next, unusedChildScopeFrame, roots id absent] using resolved, found, represented⟩
  · intro id member descriptor root declared resolved
    apply bumped.localTypes id member descriptor root declared
    simpa [next, unusedChildScopeFrame, roots id absent] using resolved
  · intro id condition root resolved
    apply bumped.uninitializedLocals id condition root
    simpa [next, unusedChildScopeFrame, roots id absent] using resolved
  · intro id condition root resolved
    apply bumped.uninitializedTypes id condition root
    simpa [next, unusedChildScopeFrame, roots id absent] using resolved
  · exact localRootCorrespondence_enterScope frame.interpretation frame.source.ctx scope state.nextScope frame.typing.visible after fresh active bumped.direct
  · intro readFuel
    exact contentRootCorrespondence_enterScope frame.interpretation frame.source.ctx scope state.nextScope frame.typing.visible readFuel config.layout after fresh active (bumped.contents readFuel)

#print axioms AcceptedFrame.enterScope_withoutDeclarations
#print axioms rootOf_enterScope_withoutDeclarations
#print axioms AcceptedFrame.releaseScope_withoutDeclarations
#print axioms runtimeScopeRoots_empty_of_noDeclarations
#print axioms AcceptedWorld.releaseScope_withoutDeclarations
end Goose.Proofs.ConstructionAcceptedExecution

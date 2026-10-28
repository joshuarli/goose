import Goose.Proofs.ConstructionAcceptedScopeWorld
import Goose.Proofs.ConstructionAcceptedCallerContents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

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

#print axioms AcceptedFrame.releaseScope_withoutDeclarations
#print axioms runtimeScopeRoots_empty_of_noDeclarations
#print axioms AcceptedWorld.releaseScope_withoutDeclarations
end Goose.Proofs.ConstructionAcceptedExecution

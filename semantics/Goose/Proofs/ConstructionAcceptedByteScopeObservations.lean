import Goose.Proofs.ConstructionAcceptedUnusedScope

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem releaseScope_withoutDeclarations_objects (state : ExecutionState) (activation : RuntimeActivation)
    (scope scopeInst : Nat)
    (absent : ∀ descriptor ∈ activation.vars.toList, descriptor.scope ≠ scope) :
    (releaseScopeState activation scope scopeInst state).objects = state.objects ∧
    (releaseScopeState activation scope scopeInst state).objectOrdinals = state.objectOrdinals := by
  have roots := runtimeScopeRoots_empty_of_noDeclarations activation scope scopeInst absent
  simp only [Goose.Proofs.Exit.runtimeScopeRoots] at roots
  simp only [releaseScopeState, roots, List.contains_nil, Bool.not_false]
  simp

theorem acceptedWorld_freshStorage_unreferenced (config : EvalConfig) (initialized : Nat)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (root : Goose.Core.RootInst) (active : live root) (value : Value)
    (found : state.objects.lookup root = some value) (stored : StoredValue)
    (occurrence : StoredOccurrence value stored) : stored.storage < state.construction.storage.size := by
  have backed := ValueStorageBacked.occurrence_backing config.layout state value (world.backing.values root active value found) stored occurrence
  cases backed with
  | detached storage element present detached type interval => exact (Array.getElem?_eq_some_iff.mp present).1
  | named id storage destination count present named binding backing type start progress element elementType interval =>
    exact (Array.getElem?_eq_some_iff.mp present).1

theorem AcceptedFrame.after_monotone_unchanged_objects
    {config : EvalConfig} {accepted : AcceptedModule config} {frame : ConstructionSourceFrame}
    {before after : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame before types)
    (objects : after.objects = before.objects) (ordinals : after.objectOrdinals = before.objectOrdinals)
    (acts : before.nextAct ≤ after.nextAct) (scopes : before.nextScope ≤ after.nextScope) :
    AcceptedFrame config accepted frame after types := by
  apply source.afterFreshActivation acts scopes
  · intro root outside
    rw [objects]
  · intro root outside
    rw [ordinals]
  · intro root outside
    rfl

#print axioms AcceptedFrame.after_monotone_unchanged_objects
#print axioms acceptedWorld_freshStorage_unreferenced
#print axioms releaseScope_withoutDeclarations_objects
end Goose.Proofs.ConstructionAcceptedExecution

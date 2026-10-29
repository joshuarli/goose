import Goose.Proofs.ConstructionExitInterruptedCleanupTrace
import Goose.Proofs.ConstructionAcceptedEntryActivation

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

namespace Goose.Proofs.ConstructionAcceptedExecution.InterruptedTrace
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

def interruptScopeFrame (state : ExecutionState) : ExecutionState :=
  { state with
    nextScope := state.nextScope + 1
    activations := state.activations.map (fun current =>
      if current.act == interruptLoopScope.act then { current with scopes := interruptLoopScope.scopes } else current) }

theorem interrupt_element_scope_frame : interruptElementJumped = interruptScopeFrame interruptWritten := by cbv

theorem interrupt_scope_accepted_world (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state ambient types live regions pending) :
    AcceptedWorld config initialized (interruptScopeFrame state) ambient types live regions pending := by
  have runtime : OwnershipRuntimeFrames (interruptScopeFrame state) ambient := by
    have result := ownershipRuntimeFrames_releaseScope interruptLoopScope 0 0 state ambient world.ownership.runtime
    exact ⟨result.activations, result.breaks⟩
  have identities : OwnershipRuntimeIdentities (interruptScopeFrame state) := by
    exact ownershipRuntimeIdentities_scopes (ownershipRuntimeIdentities_freshScope world.ownership.identities)
      interruptLoopScope interruptLoopScope.scopes
  have ownership : OwnershipExecutionContext (interruptScopeFrame state) ambient :=
    ⟨world.ownership.source, world.ownership.retention, runtime, world.ownership.reservations,
      world.ownership.receiving, world.ownership.bounds, identities⟩
  exact acceptedWorld_clockFrame config initialized state (interruptScopeFrame state) ambient types live world ownership
    rfl rfl rfl (Nat.le_refl _) (Nat.le_succ _)

theorem interrupt_element_jump_accepted_world (initialized : Nat) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld interruptConfig initialized interruptWritten ambient types live regions pending) :
    AcceptedWorld interruptConfig initialized interruptElementJumped ambient types live regions pending := by
  rw [interrupt_element_scope_frame]
  exact interrupt_scope_accepted_world interruptConfig initialized interruptWritten ambient types live regions pending world

#print axioms interrupt_element_jump_accepted_world
#print axioms interrupt_element_scope_frame
#print axioms interrupt_scope_accepted_world

end Goose.Proofs.ConstructionAcceptedExecution.InterruptedTrace

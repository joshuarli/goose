import Goose.Proofs.ConstructionAcceptedRegisterCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem AcceptedWorld.freshActivationOutside (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state ambient types live regions pending) :
    OwnershipAmbient.withoutActivation state.nextAct ambient = ambient := by
  apply List.filter_eq_self.mpr
  intro frame member
  cases frame with
  | callChannels captured carriers =>
    have inAmbient : ownershipActivationChannels captured ∈ OwnershipAmbient.activations ambient := by
      exact List.mem_filterMap.mpr ⟨.callChannels captured carriers, member, rfl⟩
    rw [← world.ownership.runtime.activations] at inAmbient
    obtain ⟨actual, inState, same⟩ := List.mem_map.mp inAmbient
    have bound := world.ownership.identities.activations.2 actual inState
    have sameAct : actual.act = captured.act := by
      simpa [ownershipActivationChannels] using congrArg OwnershipActivationChannels.act same
    simp only [bne_iff_ne, ne_eq]
    intro equal
    rw [sameAct, equal] at bound
    exact (Nat.lt_irrefl _ bound)
  | _ => rfl

#print axioms AcceptedWorld.freshActivationOutside
end Goose.Proofs.ConstructionAcceptedExecution

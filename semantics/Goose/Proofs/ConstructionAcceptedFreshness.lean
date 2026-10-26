import Goose.Proofs.ConstructionAcceptedState

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

private theorem emptyWorld_clockFrame (config : EvalConfig) (initialized : Nat)
    (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (liveRoots : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config initialized before ambient types liveRoots [] [])
    (ownership : OwnershipExecutionContext after ambient)
    (construction : after.construction = before.construction) (objects : after.objects = before.objects)
    (identities : after.objectOrdinals = before.objectOrdinals)
    (acts : before.nextAct ≤ after.nextAct) (scopes : before.nextScope ≤ after.nextScope) :
    AcceptedWorld config initialized after ambient types liveRoots [] [] := by
  refine ⟨⟨ownership, ?_, world.globalTypes, world.layouts, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, world.globalLive⟩
  · refine ⟨world.globals.1, ?_⟩
    intro id available
    obtain ⟨descriptor, value, declared, found, represented⟩ := world.globals.2 id available
    exact ⟨descriptor, value, declared, by rw [objects]; exact found, represented⟩
  · intro act scope id ty registered
    have bounded := world.typeFrontier act scope id ty registered
    exact ⟨Nat.lt_of_lt_of_le bounded.1 acts, Nat.lt_of_lt_of_le bounded.2 scopes⟩
  · intro id ty registered outside
    exact Nat.lt_of_lt_of_le (world.syntheticFrontier id ty registered outside) (Nat.add_le_add_left scopes _)
  · intro root ty value registered found
    rw [objects] at found
    exact world.heap root ty value registered found
  · intro root value found
    rw [objects] at found
    exact world.objectsRegistered root value found
  · intro root ordinal found
    rw [identities] at found
    exact world.ordinalsRegistered root ordinal found
  · constructor
    · intro root retained value found
      rw [objects] at found
      exact ValueStorageBacked.construction_frame construction (world.backing.values root retained value found)
    · intro root retained stored found
      rw [objects] at found
      rw [identities]
      exact world.backing.identities root retained stored found
  · intro region present
    cases present
  · intro frame present
    cases present

theorem freshAct_acceptedWorld (config : EvalConfig) (initialized : Nat)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (liveRoots : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config initialized state ambient types liveRoots [] []) :
    freshAct state = .ok state.nextAct { state with nextAct := state.nextAct + 1 } ∧
      AcceptedWorld config initialized { state with nextAct := state.nextAct + 1 } ambient types liveRoots [] [] := by
  refine ⟨rfl, emptyWorld_clockFrame config initialized state _ ambient types liveRoots world ?_ rfl rfl rfl
    (Nat.le_succ _) (Nat.le_refl _)⟩
  exact ⟨world.ownership.source, world.ownership.retention,
    ⟨world.ownership.runtime.activations, world.ownership.runtime.breaks⟩,
    world.ownership.reservations, world.ownership.receiving, world.ownership.bounds,
    ownershipRuntimeIdentities_freshAct world.ownership.identities⟩

theorem freshScope_acceptedWorld (config : EvalConfig) (initialized : Nat)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (liveRoots : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config initialized state ambient types liveRoots [] []) :
    freshScope state = .ok state.nextScope { state with nextScope := state.nextScope + 1 } ∧
      AcceptedWorld config initialized { state with nextScope := state.nextScope + 1 } ambient types liveRoots [] [] := by
  refine ⟨rfl, emptyWorld_clockFrame config initialized state _ ambient types liveRoots world ?_ rfl rfl rfl
    (Nat.le_refl _) (Nat.le_succ _)⟩
  exact ⟨world.ownership.source, world.ownership.retention,
    ⟨world.ownership.runtime.activations, world.ownership.runtime.breaks⟩,
    world.ownership.reservations, world.ownership.receiving, world.ownership.bounds,
    ownershipRuntimeIdentities_freshScope world.ownership.identities⟩

#print axioms freshAct_acceptedWorld
#print axioms freshScope_acceptedWorld

end Goose.Proofs.ConstructionAcceptedExecution

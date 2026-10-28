import Goose.Proofs.ConstructionAcceptedState

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

private theorem storedDestination_construction_frame (before after : ExecutionState)
    (construction : after.construction = before.construction) (id : Nat) (stored : StoredValue)
    (sampled : storedDestination id before = .ok stored before) :
    storedDestination id after = .ok stored after := by
  simp only [storedDestination, getDestination, EvalM.get, bind, pure, construction] at sampled ⊢
  cases found : before.construction.destinations[id]? with
  | none => simp [found, fault, EvalM.stop] at sampled
  | some row =>
    simp only [found] at sampled ⊢
    cases count : progressCount row.progress with
    | none => simp [count, fault, EvalM.stop] at sampled
    | some count => simp only [count, ExecutionStep.ok.injEq] at sampled ⊢; exact sampled

theorem carrierBacking_construction_frame (layout : LayoutEnv) (before after : ExecutionState)
    (construction : after.construction = before.construction) (carrier : Carrier)
    (backed : CarrierResultBacking layout before carrier) : CarrierResultBacking layout after carrier := by
  cases backed with
  | register value backed => exact .register value (ValueStorageBacked.construction_frame construction backed)
  | completed id count destination stored present built sampled backed =>
    exact .completed id count destination stored (by simpa only [construction] using present) built
      (storedDestination_construction_frame before after construction id stored sampled)
      (StoredValueBacking.construction_frame construction backed)
  | pendingNamed token incoming selected count snapshot source stored ticket present marked phase sampled backed =>
    exact .pendingNamed token incoming selected count snapshot source stored
      (by simpa only [construction] using ticket) (by simpa only [construction] using present) marked phase
      (storedDestination_construction_frame before after construction selected stored sampled)
      (StoredValueBacking.construction_frame construction backed)

private def receivingReady_construction_frame (before after : ExecutionState)
    (construction : after.construction = before.construction) (incoming source : Nat)
    (ready : ReceivingCarrierLandingReady before incoming source) :
    ReceivingCarrierLandingReady after incoming source := by
  refine ⟨ready.receiving, ready.sourceDestination, ready.receivingDestination, ?_, ?_, ?_, ?_, ?_, ready.ordered⟩
  · simpa only [construction] using ready.resolved
  · simpa only [construction] using ready.sourcePresent
  · simpa only [construction] using ready.receivingPresent
  · simpa only [construction] using ready.path
  · simpa only [construction] using ready.parent

theorem carrierReady_construction_frame (before after : ExecutionState)
    (construction : after.construction = before.construction) (channel : Channel) (carrier : Carrier)
    (ready : CarrierLandingReady before channel carrier) : CarrierLandingReady after channel carrier := by
  cases ready with
  | register ty value => exact .register ty value
  | construct incoming source ready =>
    exact .construct incoming source (receivingReady_construction_frame before after construction incoming source ready)
  | completion token incoming selected source role snapshot ticket ready =>
    exact .completion token incoming selected source role snapshot (by simpa only [construction] using ticket)
      (receivingReady_construction_frame before after construction selected source ready)
  | pendingNamed token incoming selected snapshot ticket =>
    exact .pendingNamed token incoming selected snapshot (by simpa only [construction] using ticket)
private theorem acceptedWorld_clockFrame (config : EvalConfig) (initialized : Nat)
    (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (liveRoots : Goose.Core.RootInst → Prop) {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (world : AcceptedWorld config initialized before ambient types liveRoots regions pending)
    (ownership : OwnershipExecutionContext after ambient)
    (construction : after.construction = before.construction) (objects : after.objects = before.objects)
    (identities : after.objectOrdinals = before.objectOrdinals)
    (acts : before.nextAct ≤ after.nextAct) (scopes : before.nextScope ≤ after.nextScope) :
    AcceptedWorld config initialized after ambient types liveRoots regions pending := by
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
  · intro region member
    have valid := world.protections region member
    refine ⟨?_, ?_, ?_, ?_, valid.authority, ?_⟩
    · simpa only [construction] using valid.present
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro root retained value found
        rw [objects] at found
        exact ValueStorageBacked.construction_frame construction (valid.observations.backing.values root retained value found)
      · intro root retained stored found
        rw [objects] at found
        rw [identities]
        exact valid.observations.backing.identities root retained stored found
      · intro root retained value found stored occurrence
        rw [objects] at found
        obtain ⟨storage, run, fuel, finish, present, sampled, measured, lower, upper⟩ :=
          (valid.observations.observations root retained value found stored occurrence).observed
        have current : after.construction.storage[stored.storage]? = some storage := by
          simpa only [construction] using present
        refine ⟨storage, run, fuel, finish, current, ?_, measured, lower, upper⟩
        exact sampledStored_storage_transport stored before after storage storage run present current rfl
          (by intro id named; simp only [construction]) sampled
    · intro row found
      exact valid.cutoff row (by simpa only [construction] using found)
    · intro row found
      exact valid.landing row (by simpa only [construction] using found)
    · intro root retained outside value found stored occurrence id named
      exact valid.names root retained outside value (by rw [objects] at found; exact found) stored occurrence id named
  · intro frame member
    obtain ⟨ready, backing⟩ := world.carriers frame member
    exact ⟨⟨ready.lengths, fun channel carrier pair =>
      carrierReady_construction_frame before after construction channel carrier (ready.pairs channel carrier pair)⟩,
      fun carrier present => carrierBacking_construction_frame config.layout before after construction carrier (backing carrier present)⟩

theorem freshAct_acceptedWorld (config : EvalConfig) (initialized : Nat)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (liveRoots : Goose.Core.RootInst → Prop) {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (world : AcceptedWorld config initialized state ambient types liveRoots regions pending) :
    freshAct state = .ok state.nextAct { state with nextAct := state.nextAct + 1 } ∧
      AcceptedWorld config initialized { state with nextAct := state.nextAct + 1 } ambient types liveRoots regions pending := by
  refine ⟨rfl, acceptedWorld_clockFrame config initialized state _ ambient types liveRoots world ?_ rfl rfl rfl
    (Nat.le_succ _) (Nat.le_refl _)⟩
  exact ⟨world.ownership.source, world.ownership.retention,
    ⟨world.ownership.runtime.activations, world.ownership.runtime.breaks⟩,
    world.ownership.reservations, world.ownership.receiving, world.ownership.bounds,
    ownershipRuntimeIdentities_freshAct world.ownership.identities⟩

theorem freshScope_acceptedWorld (config : EvalConfig) (initialized : Nat)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (liveRoots : Goose.Core.RootInst → Prop) {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (world : AcceptedWorld config initialized state ambient types liveRoots regions pending) :
    freshScope state = .ok state.nextScope { state with nextScope := state.nextScope + 1 } ∧
      AcceptedWorld config initialized { state with nextScope := state.nextScope + 1 } ambient types liveRoots regions pending := by
  refine ⟨rfl, acceptedWorld_clockFrame config initialized state _ ambient types liveRoots world ?_ rfl rfl rfl
    (Nat.le_refl _) (Nat.le_succ _)⟩
  exact ⟨world.ownership.source, world.ownership.retention,
    ⟨world.ownership.runtime.activations, world.ownership.runtime.breaks⟩,
    world.ownership.reservations, world.ownership.receiving, world.ownership.bounds,
    ownershipRuntimeIdentities_freshScope world.ownership.identities⟩

#print axioms freshAct_acceptedWorld
#print axioms freshScope_acceptedWorld

end Goose.Proofs.ConstructionAcceptedExecution

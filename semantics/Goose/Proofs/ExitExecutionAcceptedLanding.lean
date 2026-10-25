import Goose.Proofs.ConstructionAcceptedState
import Goose.Proofs.ExitExecutionLiveCarrierLanding

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionAcceptedExecution

private theorem protectedCleanup_backing (layout : LayoutEnv) (before after : ExecutionState)
    (retained : RootInst → Prop) (limit : Nat → Nat)
    (valid : RootedBackingObservations layout before retained limit) (cuts : List CleanupStorageBoundary)
    (trace : CleanupStorageTrace cuts before.construction.storage after.construction.storage)
    (geometry : ∀ cut ∈ cuts, limit cut.storage ≤ cut.retainedEnd)
    (objects : after.objects = before.objects) (ordinals : after.objectOrdinals = before.objectOrdinals)
    (rows : ∀ root, retained root → ∀ value, before.objects.lookup root = some value →
      ∀ stored, StoredOccurrence value stored → ∀ id, stored.destination = some id →
      after.construction.destinations[id]? = before.construction.destinations[id]?) :
    RootedBackingObservations layout after retained limit := by
  let bounded := fun id => min (limit id)
    ((before.construction.storage[id]?.map fun storage => storage.bytes.size).getD 0)
  have boundedValid : RootedBackingObservations layout before retained bounded :=
    rootedBackingObservations_bytes_bound layout before retained limit valid
  have prefixes := trace.prefixes bounded (by
    intro cut member
    exact Nat.le_trans (Nat.min_le_left _ _) (geometry cut member))
  have frame : RootedBackingPrefixFrame before after retained bounded := by
    refine ⟨fun _ _ => by rw [objects], fun _ _ => by rw [ordinals], ?_⟩
    intro root kept value found stored occurrence
    have backing := (valid.backing.values root kept value found).occurrence_backing layout before value stored occurrence
    obtain ⟨storage, run, present, sampled, interval⟩ := backing.sampled layout before stored
    obtain ⟨current, currentFound, count, bytes⟩ := prefixes.lookup _ _ _ stored.storage storage present
    refine ⟨⟨storage, current, present, currentFound, ?_, count⟩, rows root kept value found stored occurrence⟩
    apply BytePrefixEqual.of_extract_eq
    · simp only [bounded, present, Option.map_some, Option.getD_some]
      exact Nat.min_le_right _ _
    · exact bytes
  have moved := boundedValid.prefix_frame layout before after retained bounded frame
  refine ⟨moved.backing, ?_⟩
  intro root kept value found stored occurrence
  obtain ⟨storage, run, fuel, finish, present, sampled, measured, lower, upper⟩ :=
    (moved.observations root kept value found stored occurrence).observed
  exact ⟨storage, run, fuel, finish, present, sampled, measured, lower,
    Nat.le_trans upper (Nat.min_le_left _ _)⟩

theorem landCarriersInto_construct_protected (module : Goose.Construct.Module) (accepted : validate module = .ok ())
    (origin : OriginId) (state : ExecutionState) (ambient : OwnershipAmbient) (incoming source : Nat)
    (liveRoots : RootInst → Prop) (region : ReceivingRegion)
    (context : OwnershipExecutionContext state ambient)
    (backed : CarrierResultBacking (.ofModule module) state (.completed source))
    (ready : ReceivingCarrierLandingReady state incoming source)
    (protection : ReceivingProtection (.ofModule module) state liveRoots region)
    (receivingRegion : region.destination = ready.receiving)
    (sourceMutable : source ∈ region.mutableDestinations)
    (abandonedMutable : ∀ row ∈ protectedRows state.construction ready.receiving source,
      row.capability.id ∈ region.mutableDestinations)
    (parentMutable : ∀ parent, ready.receivingDestination.use = .child parent ∨
      ready.receivingDestination.use = .replacement parent → parent ∈ region.mutableDestinations) :
    ∃ after, landCarriersInto origin [.construct incoming] [.completed source] state = .ok () after ∧
      CarrierResultBacking (.ofModule module) after (.completed source) ∧
      CarrierLandingReady after (.construct incoming) (.completed source) ∧
      after.construction.exitReservations = state.construction.exitReservations ∧
      RootedBackingObservations (.ofModule module) after
        (fun root => liveRoots root ∧ ¬ region.mutableRoots root) region.limit ∧
      after.construction.stdout = state.construction.stdout ∧
      ∀ (fuel : Nat) (location : Loc), liveRoots location.root → ¬ region.mutableRoots location.root →
        mapStepState (fun _ => ExecutionState.initial) (readLoc fuel (.ofModule module) location after) =
          mapStepState (fun _ => ExecutionState.initial) (readLoc fuel (.ofModule module) location state) := by
  obtain ⟨after, success, sourceBacked, ⟨postReady⟩, tickets, frame⟩ :=
    landCarriersInto_construct_completed (.ofModule module) origin state ambient incoming source context backed ready
  refine ⟨after, success, sourceBacked, .construct incoming source postReady, tickets, ?_⟩
  cases frame with
  | current => exact ⟨protection.observations, rfl, by intros; rfl⟩
  | commit receiving count replacement anchor storage parentUpdate chain resolved present built receivingPresent
      stored sameStorage ordered inside parentBound parentDifferent parentFootprint =>
    have receivingSame : receiving = ready.receiving := Except.ok.inj (resolved.symm.trans ready.resolved)
    have anchorSame : anchor = ready.receivingDestination := by
      exact Option.some.inj (receivingPresent.symm.trans (by simpa only [receivingSame] using ready.receivingPresent))
    have actualRegion : region.destination = receiving := receivingRegion.trans receivingSame.symm
    have landingCut : region.limit replacement.storage ≤ anchor.capability.start := by
      rw [← sameStorage]
      exact protection.landing anchor (by simpa only [actualRegion] using receivingPresent)
    let after : ExecutionState := { state with construction := (committedExitState state.construction
      source receiving count replacement anchor storage parentUpdate chain) }
    have trace : CleanupStorageTrace [⟨replacement.storage, anchor.capability.start⟩]
        state.construction.storage after.construction.storage := by
      change CleanupStorageTrace _ _ (completedLandingState state.construction source receiving count replacement anchor storage parentUpdate).storage
      rw [completedLandingState_storage]
      exact .rewrite state.construction.storage replacement.storage storage
        (storage.landExit anchor.capability.start replacement.capability.start) anchor.capability.start
        stored rfl (landingBytes_prefix storage.bytes anchor.capability.start replacement.capability.start ordered inside).bytes
    have geometry : ∀ (cut : CleanupStorageBoundary), cut ∈ [⟨replacement.storage, anchor.capability.start⟩] → region.limit cut.storage ≤ cut.retainedEnd := by
      intro cut member
      simp only [List.mem_singleton] at member
      cases member
      exact landingCut
    have rowFrame : ∀ root, liveRoots root ∧ ¬ region.mutableRoots root → ∀ value,
        state.objects.lookup root = some value → ∀ storedValue, StoredOccurrence value storedValue →
        ∀ id, storedValue.destination = some id → after.construction.destinations[id]? = state.construction.destinations[id]? := by
      intro root retained value found storedValue occurrence id named
      have outside := protection.names root retained.1 retained.2 value found storedValue occurrence id named
      apply completedLandingState_outside_destination state.construction source receiving count replacement anchor storage parentUpdate id
      · intro same
        exact outside (by simpa only [same] using sourceMutable)
      · intro row member same
        exact outside (by simpa only [same] using abandonedMutable row (by simpa only [receivingSame] using member))
      · intro parentId parent updated same
        have owned := parentMutable parentId (by simpa only [anchorSame] using parentFootprint parentId parent updated)
        exact outside (by simpa only [same] using owned)
    refine ⟨protectedCleanup_backing (.ofModule module) state after _ region.limit protection.observations _ trace
        geometry rfl rfl rowFrame,
      completedLandingState_stdout state.construction source receiving count replacement anchor storage parentUpdate, ?_⟩
    intro fuel location live immutable
    exact cleanupStorageTrace_rooted_read_observation fuel module accepted state after
      (fun root => liveRoots root ∧ ¬ region.mutableRoots root) region.limit protection.observations
      [⟨replacement.storage, anchor.capability.start⟩] trace geometry (fun _ _ => rfl)
      rowFrame location ⟨live, immutable⟩

theorem landCarriersInto_completion_protected (module : Goose.Construct.Module) (accepted : validate module = .ok ())
    (origin : OriginId) (state : ExecutionState) (ambient : OwnershipAmbient)
    (token incoming selected source : Nat) (role : ExitReservationRole) (snapshot : PendingDestination)
    (liveRoots : RootInst → Prop) (region : ReceivingRegion)
    (context : OwnershipExecutionContext state ambient)
    (ticket : state.construction.exitReservations[token]? = some (.active role incoming selected snapshot))
    (backed : CarrierResultBacking (.ofModule module) state (.completed source))
    (ready : ReceivingCarrierLandingReady state selected source)
    (protection : ReceivingProtection (.ofModule module) state liveRoots region)
    (receivingRegion : region.destination = ready.receiving)
    (sourceMutable : source ∈ region.mutableDestinations)
    (abandonedMutable : ∀ row ∈ protectedRows state.construction ready.receiving source,
      row.capability.id ∈ region.mutableDestinations)
    (parentMutable : ∀ parent, ready.receivingDestination.use = .child parent ∨
      ready.receivingDestination.use = .replacement parent → parent ∈ region.mutableDestinations) :
    ∃ after, landCarriersInto origin [.completion token] [.completed source] state = .ok () after ∧
      CarrierResultBacking (.ofModule module) after (.completed source) ∧
      CarrierLandingReady after (.completion token) (.completed source) ∧
      RootedBackingObservations (.ofModule module) after
        (fun root => liveRoots root ∧ ¬ region.mutableRoots root) region.limit ∧
      after.construction.stdout = state.construction.stdout ∧
      ∀ (fuel : Nat) (location : Loc), liveRoots location.root → ¬ region.mutableRoots location.root →
        mapStepState (fun _ => ExecutionState.initial) (readLoc fuel (.ofModule module) location after) =
          mapStepState (fun _ => ExecutionState.initial) (readLoc fuel (.ofModule module) location state) := by
  obtain ⟨after, success, sourceBacking, postReady, tickets, observations, stdout, reads⟩ :=
    landCarriersInto_construct_protected module accepted origin state ambient selected source liveRoots region
      context backed ready protection receivingRegion sourceMutable abandonedMutable parentMutable
  cases postReady with
  | construct _ _ actualReady =>
    refine ⟨after, ?_, sourceBacking, .completion token incoming selected source role snapshot ?_ actualReady,
      observations, stdout, reads⟩
    · simpa only [landCarriersInto, List.length_cons, List.length_nil, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons,
        List.forIn_nil, EvalM.get, ticket, bind, pure] using success
    · simpa only [tickets] using ticket

#print axioms landCarriersInto_construct_protected
#print axioms landCarriersInto_completion_protected

end Goose.Proofs.ExitExecution

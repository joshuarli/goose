import Goose.Proofs.ConstructionExitFreshCancelLifecycle

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem allocated_receiver_cancel_source_roles (config : EvalConfig) (initialized : Nat) (owner : ActId)
    (ty element : Goose.Construct.Ty) (request : ConstructionRequest) (origin : OriginId) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (elementType : Goose.Construct.elementType ty = some element)
    (created : newDestination config.layout owner ty request origin none knownCount before = .ok id allocated) :
    ∃ reserved final,
      reserveExitDestination id .newValue allocated.construction = .ok (allocated.construction.exitReservations.size, id) reserved ∧
      (do
        cancelExitReservation allocated.construction.exitReservations.size []
        releaseExitReservation allocated.construction.exitReservations.size) reserved = .ok () final ∧
      ReservationLifecycleInvariant final ∧ DestinationSuccessorsValid final ∧ DestinationSuccessorKeysInactive final ∧
      LiveFreshReservationSuccessorRoles final ∧ LiveFreshReservationRawRoles final ∧ LiveFreshReservationRoles final ∧
      ResumptionReservationRoles final ∧ ResumptionSnapshotStart final ∧ ResumptionBackingSources final ∧ UnsupportedResumptionKeys final ∧ SupportedReplacementAuthority final ∧
      RootedBackingObservations config.layout { allocated with construction := final } live (storageExtent before) ∧
      (∀ region ∈ regions, ReceivingProtection config.layout { allocated with construction := final } live region) ∧
      ∀ frame ∈ pending, CarriersLandingReady { allocated with construction := final } frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout { allocated with construction := final } carrier := by
  obtain ⟨reserved, final, reserve, cancel, lifecycle, rooted, regionsSafe, frames⟩ :=
    allocated_receiver_cancel_lifecycle config initialized owner ty element request origin knownCount before allocated id ambient types live
      regions pending world elementType created
  obtain ⟨otherReserved, otherFinal, otherReserve, otherCancel, savedSnapshot, ⟨frame⟩, savedEntries, savedOpened, savedUse, abandonedFound, savedPresent, savedRows⟩ :=
    allocated_receiver_cancel_exact_frame config initialized owner ty element request origin knownCount before allocated id ambient types live
      regions pending world elementType created
  have sameReserved : otherReserved = reserved := (ConstructionResult.ok.inj (otherReserve.symm.trans reserve)).2
  subst otherReserved
  have sameFinal : otherFinal = final := (ConstructionResult.ok.inj (otherCancel.symm.trans cancel)).2
  subst otherFinal
  have successors : DestinationSuccessorsValid final := by
    intro key next edge
    have maps : final.destinationSuccessors = before.construction.destinationSuccessors := frame.successors
    have originalEdge : before.construction.destinationSuccessors.lookup key = some next := by
      simpa only [maps] using edge
    obtain ⟨ordered, bounded⟩ := world.ownership.source.structural.2.1 key next originalEdge
    exact ⟨ordered, Nat.lt_of_lt_of_le bounded frame.size⟩
  have inactive : DestinationSuccessorKeysInactive final := by
    intro key next edge
    have maps : final.destinationSuccessors = before.construction.destinationSuccessors := frame.successors
    have originalEdge : before.construction.destinationSuccessors.lookup key = some next := by
      simpa only [maps] using edge
    obtain ⟨row, present, inactive⟩ := world.ownership.source.inactiveKeys key next originalEdge
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    exact ⟨row, (frame.lookup key inside).trans present, inactive⟩
  have aliases : LiveFreshReservationSuccessorRoles final := by
    intro token incoming selected node snapshot destination ticket path present
    have tickets : final.exitReservations = before.construction.exitReservations.push .released := frame.tickets
    have oldTicket : before.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot) := by
      simp only [tickets, Array.getElem?_push] at ticket
      split at ticket
      · cases ticket
      · exact ticket
    have maps : final.destinationSuccessors = before.construction.destinationSuccessors := frame.successors
    have oldPath : DestinationSuccessorPath before.construction selected node :=
      DestinationSuccessorPath.congr maps.symm path
    have selectedBound := (world.ownership.source.structural.1.1.2.active token .fresh incoming selected snapshot oldTicket).2.1
    have nodeBound := oldPath.bound world.ownership.source.structural.2.1 selectedBound
    have oldPresent : before.construction.destinations[node]? = some destination :=
      (frame.lookup node nodeBound).symm.trans present
    exact world.ownership.source.aliases token incoming selected node snapshot destination oldTicket oldPath oldPresent
  have resumptions : ResumptionReservationRoles final := by
    intro key saved savedFound token incoming selected snapshot ticket resolved
    have tickets : final.exitReservations = before.construction.exitReservations.push .released := frame.tickets
    have oldTicket : before.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot) := by
      simp only [tickets, Array.getElem?_push] at ticket
      split at ticket
      · cases ticket
      · exact ticket
    have selectedBound := (world.ownership.source.structural.1.1.2.active token .fresh incoming selected snapshot oldTicket).2.1
    obtain ⟨oldCurrent, oldResolved, _, oldBound, _⟩ := destinationCurrent_total before.construction
      world.ownership.source.structural.2.1 selected selectedBound
    have maps : final.destinationSuccessors = before.construction.destinationSuccessors := frame.successors
    have finalResolved := destinationCurrent_extension before.construction final maps frame.size selected oldCurrent oldResolved
    have keyEqual : key = oldCurrent := Except.ok.inj (resolved.symm.trans finalResolved)
    have fresh := newDestination_fresh_id config.layout owner ty request origin knownCount before allocated id created
    have different : key ≠ id := by
      rw [keyEqual, fresh]
      exact Nat.ne_of_lt oldBound
    have mismatch : (key == id) = false := beq_eq_false_iff_ne.mpr different
    have oldSaved : allocated.construction.destinationResumptions.lookup key = some saved := by
      simpa [savedEntries, List.lookup, mismatch] using savedFound
    obtain ⟨allocation⟩ := newDestination_fresh_frame config.layout owner ty request origin knownCount before allocated id
      world.ownership.source.structural.1.1.1 created
    have allocatedTicket : allocated.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot) := by
      rw [allocation.tickets]
      exact oldTicket
    have allocatedResolved := destinationCurrent_extension before.construction allocated.construction allocation.successors
      allocation.size selected oldCurrent oldResolved
    have allocatedWorld := newDestination_acceptedWorld config owner ty request origin knownCount initialized before allocated id
      ambient types live regions pending world created
    apply allocatedWorld.ownership.source.resumptionRoles key saved oldSaved token incoming selected snapshot allocatedTicket
    simpa only [keyEqual] using allocatedResolved
  have allocatedWorld := newDestination_acceptedWorld config owner ty request origin knownCount initialized before allocated id
    ambient types live regions pending world created
  obtain ⟨allocation⟩ := newDestination_fresh_frame config.layout owner ty request origin knownCount before allocated id
    world.ownership.source.structural.1.1.1 created
  have fresh := newDestination_fresh_id config.layout owner ty request origin knownCount before allocated id created
  have newest := (newDestination_newest_receiver config.layout owner ty request origin knownCount before allocated id created).1
  have savedStart : ResumptionSnapshotStart final := by
    intro key saved found
    by_cases same : key = id
    · subst key
      have equal : savedSnapshot = saved := by simpa [savedEntries, List.lookup] using found
      simpa only [← equal] using savedOpened
    · have mismatch : (key == id) = false := beq_eq_false_iff_ne.mpr same
      have old : allocated.construction.destinationResumptions.lookup key = some saved := by
        simpa [savedEntries, List.lookup, mismatch] using found
      exact allocatedWorld.ownership.source.structural.1.2.1.2.2.2.2.2.2 key saved old
  have savedBacking : ResumptionBackingSources final := by
    intro key saved found
    by_cases same : key = id
    · subst key
      have equal : savedSnapshot = saved := by simpa [savedEntries, List.lookup] using found
      subst saved
      exact ⟨{ savedSnapshot with progress := .abandoned }, abandonedFound, by simp [activeProgress], by simp [SnapshotBackingAgrees, savedUse]⟩
    · have mismatch : (key == id) = false := beq_eq_false_iff_ne.mpr same
      have old : allocated.construction.destinationResumptions.lookup key = some saved := by
        simpa [savedEntries, List.lookup, mismatch] using found
      obtain ⟨row, present, inactive, sameBacking⟩ := allocatedWorld.ownership.source.structural.1.2.2.2.1 key saved old
      have bound := (Array.getElem?_eq_some_iff.mp present).1
      have keyLe : key ≤ id := Nat.lt_succ_iff.mp (by simpa only [newest] using bound)
      have keyLt : key < id := Nat.lt_of_le_of_ne keyLe same
      have oldBound : key < before.construction.destinations.size := by simpa only [fresh] using keyLt
      have foundAfter : final.destinations[key]? = some row :=
        (frame.lookup key oldBound).trans ((allocation.lookup key oldBound).symm.trans present)
      exact ⟨row, foundAfter, inactive, sameBacking⟩
  have unsupported : UnsupportedResumptionKeys final := by
    intro key saved found support
    by_cases same : key = id
    · subst key
      cases support with
      | active index row present active =>
        have equal : row = { savedSnapshot with progress := .abandoned } := Option.some.inj (present.symm.trans abandonedFound)
        subst row
        simp [activeProgress] at active
      | parent child parent row present use supported =>
        have ordered : id < child := by simpa only [use] using lifecycle.1.2.2.2 child row present
        have bound := (Array.getElem?_eq_some_iff.mp present).1
        have finalSize : final.destinations.size = before.construction.destinations.size + 1 := by
          simpa only [Array.size_push] using congrArg Array.size frame.destinations
        rw [finalSize, ← fresh] at bound
        omega
    · have mismatch : (key == id) = false := beq_eq_false_iff_ne.mpr same
      have old : allocated.construction.destinationResumptions.lookup key = some saved := by
        simpa [savedEntries, List.lookup, mismatch] using found
      have setSupport : ReplacementSupported { allocated.construction with
          destinations := allocated.construction.destinations.set! id { savedSnapshot with progress := .abandoned } } key :=
        replacementSupported_congr_destinations final _ savedRows.symm key support
      have prior : ReplacementSupported allocated.construction key := by
        apply replacementSupported_replace_back allocated.construction id savedSnapshot
          { savedSnapshot with progress := .abandoned } savedPresent _ _ key setSupport
        · intro parent use; exact use
        · intro active; simp [activeProgress] at active
      exact allocatedWorld.ownership.source.structural.1.2.2.2.2.1 key saved old prior
  have authority : SupportedReplacementAuthority final := by
    have prior := supportedReplacementAuthority_replace_inactive allocated.construction id savedSnapshot
      { savedSnapshot with progress := .abandoned } savedPresent rfl rfl (Or.inr (Or.inl rfl))
      allocatedWorld.ownership.source.structural.1.2.2.1
    exact supportedReplacementAuthority_congr_destinations _ final savedRows prior
  exact ⟨reserved, final, reserve, cancel, lifecycle, successors, inactive, aliases,
    liveFreshReservationSuccessorRoles_raw final aliases, liveFreshReservationSuccessorRoles_current final aliases, resumptions, savedStart, savedBacking, unsupported, authority,
    rooted, regionsSafe, frames⟩

#print axioms allocated_receiver_cancel_source_roles

end Goose.Proofs.ConstructionAcceptedExecution

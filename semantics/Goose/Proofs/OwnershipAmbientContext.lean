import Goose.Proofs.OwnershipScopeDesignFrontiers
import Goose.Proofs.ConstructionExecutionOwnershipResumptionBacking
import Goose.Proofs.ConstructionExecutionProtocolReservations
import Goose.Proofs.OwnershipReceivingPrefixContext
import Goose.Proofs.OwnershipEvaluationActions

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

inductive OwnershipAmbientFrame
  | resultScope (channels : List Channel) (flow : Construct.Flow) (carriers : List Construct.Carrier)
  | exitChannels (tokens : List ExitReservationId) (channels : List Channel) (carriers : List Construct.Carrier)
  | completionChannels (tokens : List ExitReservationId) (channels : List Channel) (carriers : List Construct.Carrier)
  | callChannels (activation : RuntimeActivation) (carriers : List Construct.Carrier)
  | breakTarget (target : BreakTarget) (carriers : List Construct.Carrier)
  | receivingScope (capture : OwnershipReceivingCapture) (carriers : List Construct.Carrier)
  | returned (carriers : List Construct.Carrier)

def OwnershipAmbientFrame.carriers : OwnershipAmbientFrame → List Construct.Carrier
  | .resultScope _ _ carriers | .exitChannels _ _ carriers | .completionChannels _ _ carriers
  | .callChannels _ carriers | .breakTarget _ carriers | .receivingScope _ carriers
  | .returned carriers => carriers

def OwnershipAmbientFrame.tickets : OwnershipAmbientFrame → List ExitReservationId
  | .exitChannels tokens _ _ | .completionChannels tokens _ _ => tokens
  | .resultScope _ _ _ | .callChannels _ _ | .breakTarget _ _ | .receivingScope _ _ | .returned _ => []

def OwnershipAmbientFrame.withCarriers : OwnershipAmbientFrame → List Construct.Carrier → OwnershipAmbientFrame
  | .resultScope channels flow _, carriers => .resultScope channels flow carriers
  | .exitChannels tokens channels _, carriers => .exitChannels tokens channels carriers
  | .completionChannels tokens channels _, carriers => .completionChannels tokens channels carriers
  | .callChannels activation _, carriers => .callChannels activation carriers
  | .breakTarget target _, carriers => .breakTarget target carriers
  | .receivingScope capture _, carriers => .receivingScope capture carriers
  | .returned _, carriers => .returned carriers

abbrev OwnershipAmbient := List OwnershipAmbientFrame

def OwnershipAmbient.retained (ambient : OwnershipAmbient) : List Construct.Carrier :=
  ambient.flatMap OwnershipAmbientFrame.carriers

def completedCarrierIds (carriers : List Construct.Carrier) : List DestinationId :=
  carriers.filterMap fun carrier => match carrier with
    | .completed id => some id
    | _ => none

def LiveFreshReservationRoles (state : ConstructionState) : Prop :=
  ∀ (token : ExitReservationId) (incoming reserved current : DestinationId)
    (snapshot selected : PendingDestination),
    state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
    destinationCurrent state reserved = .ok current → state.destinations[current]? = some selected →
    if reserved = snapshot.capability.id then
      selected.use = snapshot.use ∧ SnapshotBackingAgrees snapshot selected
    else selected.use = .replacement snapshot.capability.id ∧ selected.backing = snapshot.backing

def OwnershipStructural (state : ConstructionState) : Prop :=
  ReservationLifecycleInvariant state ∧ ConstructionOwnershipLinks state ∧
    SupportedReplacementAuthority state ∧ ResumptionBackingSources state ∧
    UnsupportedResumptionKeys state ∧ LiveFreshReservationRoles state

def RetainedReplacementAnchors (state : ConstructionState) (carriers : List Construct.Carrier) : Prop :=
  ∀ (id : DestinationId) (row : PendingDestination), state.destinations[id]? = some row →
    activeProgress row.progress = false → ReplacementSupported state id →
    ∃ retained, retained ∈ completedCarrierIds carriers ∧
      destinationDescendant state.destinations id retained = true

def RetainedOutsideTickets (state : ConstructionState) (tokens : List ExitReservationId)
    (carriers : List Construct.Carrier) : Prop :=
  ∀ (token : ExitReservationId) (incoming reserved selected : DestinationId) (snapshot : PendingDestination),
    token ∈ tokens →
    state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
    destinationCurrent state reserved = .ok selected →
    ∀ retained ∈ completedCarrierIds carriers,
      destinationDescendant state.destinations selected retained = false

def OwnershipAmbientBoundaries (state : ConstructionState) : OwnershipAmbient → Prop
  | [] => True
  | frame :: outer => RetainedOutsideTickets state frame.tickets (OwnershipAmbient.retained outer) ∧
      OwnershipAmbientBoundaries state outer

structure OwnershipAmbientInvariant (state : ConstructionState) (ambient : OwnershipAmbient) : Prop where
  structural : OwnershipStructural state
  anchors : RetainedReplacementAnchors state ambient.retained
  boundaries : OwnershipAmbientBoundaries state ambient

def OwnershipAmbientOutcome (ambient : OwnershipAmbient) (shape : OwnershipResultShape α) :
    ExecutionStep α → Prop
  | .ok value state => OwnershipAmbientInvariant state.construction
      (.returned (shape.retainedCarriers value) :: ambient)
  | .stop _ state => OwnershipStructural state.construction
  | .escape _ carriers state => OwnershipAmbientInvariant state.construction (.returned carriers :: ambient)
  | .jump _ (.breakValue carriers) state => OwnershipAmbientInvariant state.construction (.returned carriers :: ambient)
  | .jump _ .continueLoop state => OwnershipAmbientInvariant state.construction ambient

theorem initial_ownershipStructural : OwnershipStructural .initial :=
  ⟨initial_reservation_lifecycle_invariant, initial_constructionOwnershipLinks,
    initial_supportedReplacementAuthority, initial_resumptionBackingSources, initial_unsupportedResumptionKeys,
    by intro token incoming reserved current snapshot selected ticket; simp [ConstructionState.initial] at ticket⟩

theorem initial_ownershipAmbientInvariant : OwnershipAmbientInvariant .initial [] := by
  refine ⟨initial_ownershipStructural, ?_, trivial⟩
  intro id row present
  simp [ConstructionState.initial] at present

theorem ownershipAmbientInvariant_congr_construction (before after : ConstructionState)
    (same : after = before) (ambient : OwnershipAmbient)
    (valid : OwnershipAmbientInvariant before ambient) : OwnershipAmbientInvariant after ambient :=
  same ▸ valid

theorem ownershipAmbientOutcome_releaseScopeState (environment : RuntimeActivation)
    (scope : Nat) (scopeInst : ScopeInst) (ambient : OwnershipAmbient) (shape : OwnershipResultShape α)
    (result : ExecutionStep α) (valid : OwnershipAmbientOutcome ambient shape result) :
    OwnershipAmbientOutcome ambient shape
      (mapStepState (releaseScopeState environment scope scopeInst) result) := by
  cases result with
  | ok value state | stop reason state | escape address carriers state => exact valid
  | jump target kind state => cases kind <;> exact valid

#print axioms initial_ownershipAmbientInvariant
#print axioms ownershipAmbientOutcome_releaseScopeState

end Goose.Proofs.ConstructionExecutionOwnership

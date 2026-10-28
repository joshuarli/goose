import Goose.Proofs.ConstructionExitBorrowedBounds

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionRepresentation

theorem receiving_within_after_waiting_update (state : ConstructionState) (token incoming : Nat)
    (outer : OwnershipAmbient) (receiving : Nat)
    (valid : OwnershipReceivingWithinSuccessorFrames state outer receiving) :
    OwnershipReceivingWithinSuccessorFrames { state with exitReservations := state.exitReservations.set! token (.waiting incoming) } outer receiving := by
  intro frame member index owned source selected snapshot node ticket path ancestry
  have old := waiting_update_active_preimage state token incoming index .fresh source selected snapshot ticket
  exact valid frame member index owned source selected snapshot node old
    (DestinationSuccessorPath.congr (before := { state with exitReservations := state.exitReservations.set! token (.waiting incoming) }) (after := state) rfl path) ancestry

theorem channel_frames_after_named_rearm (state : ConstructionState) (token incoming selected current : Nat)
    (stage : NamedReservationStage) (source : Nat) (snapshot : PendingDestination) (outer : OwnershipAmbient)
    (ticket : state.exitReservations[token]? = some (.active (.named stage) source selected snapshot))
    (incomingCurrent : destinationCurrent state incoming = .ok current)
    (selectedCurrent : destinationCurrent state selected = .ok current)
    (channel : Channel) (valid : OwnershipChannelReceivingWithinFrames state outer channel) :
    OwnershipChannelReceivingWithinFrames { state with exitReservations := state.exitReservations.set! token (.waiting incoming) } outer channel := by
  let after := { state with exitReservations := state.exitReservations.set! token (.waiting incoming) }
  have currentBefore (id receiving : Nat) (found : destinationCurrent after id = .ok receiving) :
      destinationCurrent state id = .ok receiving := by
    exact (destinationCurrent_congr_tables state after rfl rfl id).symm.trans found
  cases channel with
  | register ty => trivial
  | construct id =>
    intro receiving found
    exact receiving_within_after_waiting_update state token incoming outer receiving (valid receiving (currentBefore id receiving found))
  | completion index =>
    constructor
    · intro oldIncoming found receiving currentFound
      by_cases same : token = index
      · subst index
        have inside := (Array.getElem?_eq_some_iff.mp found).1
        have now : after.exitReservations[token]? = some (.waiting incoming) := by
          simp only [after, Array.set!_eq_setIfInBounds]
          exact Array.getElem?_setIfInBounds_self_of_lt (by simpa using inside)
        have equal := Option.some.inj (found.symm.trans now)
        cases equal
        have beforeCurrent := currentBefore incoming receiving currentFound
        have sameReceiving : receiving = current := Except.ok.inj (beforeCurrent.symm.trans incomingCurrent)
        subst receiving
        exact receiving_within_after_waiting_update state token incoming outer current
          (valid.2 (.named stage) source selected snapshot ticket current selectedCurrent)
      · have old : state.exitReservations[index]? = some (.waiting oldIncoming) := by
          simpa [after, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, same] using found
        exact receiving_within_after_waiting_update state token incoming outer receiving
          (valid.1 oldIncoming old receiving (currentBefore oldIncoming receiving currentFound))
    · intro role oldIncoming oldSelected oldSnapshot found receiving currentFound
      have old := waiting_update_active_preimage state token incoming index role oldIncoming oldSelected oldSnapshot found
      exact receiving_within_after_waiting_update state token incoming outer receiving
        (valid.2 role oldIncoming oldSelected oldSnapshot old receiving (currentBefore oldSelected receiving currentFound))

theorem captured_frames_after_named_rearm (state : ConstructionState) (token incoming selected current : Nat)
    (stage : NamedReservationStage) (source : Nat) (snapshot : PendingDestination) (ambient : OwnershipAmbient)
    (ticket : state.exitReservations[token]? = some (.active (.named stage) source selected snapshot))
    (incomingCurrent : destinationCurrent state incoming = .ok current)
    (selectedCurrent : destinationCurrent state selected = .ok current)
    (valid : OwnershipCapturedReceivingFrames state ambient) :
    OwnershipCapturedReceivingFrames { state with exitReservations := state.exitReservations.set! token (.waiting incoming) } ambient := by
  induction ambient with
  | nil => trivial
  | cons frame outer ih =>
    have tail := ih valid.2
    refine ⟨?_, tail⟩
    cases frame <;> try trivial
    case receivingScope capture carriers =>
      exact channel_frames_after_named_rearm state token incoming selected current stage source snapshot outer ticket incomingCurrent selectedCurrent (.construct capture.incoming) valid.1
    all_goals intro channel member; exact channel_frames_after_named_rearm state token incoming selected current stage source snapshot outer ticket incomingCurrent selectedCurrent channel (valid.1 channel member)

theorem named_rearm_context (state : ExecutionState) (receipt : BorrowedWaitingExitReservation)
    (stage : NamedReservationStage) (incoming selected current : Nat) (snapshot row : PendingDestination)
    (ambient : OwnershipAmbient)
    (ticket : state.construction.exitReservations[receipt.token]? = some (.active (.named stage) incoming selected snapshot))
    (incomingCurrent : destinationCurrent state.construction receipt.incoming = .ok current)
    (selectedCurrent : destinationCurrent state.construction selected = .ok current)
    (present : state.construction.destinations[current]? = some row)
    (context : OwnershipExecutionContext state ambient) :
    OwnershipExecutionContext { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! receipt.token (.waiting receipt.incoming) } } ambient := by
  let after := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! receipt.token (.waiting receipt.incoming) } }
  have source := waiting_update_source state.construction receipt stage incoming selected current snapshot row ticket incomingCurrent present context.source
  have bounds := captured_bounds_after_waiting_update state.construction receipt.token receipt.incoming current ambient incomingCurrent context.bounds
  have receiving := captured_frames_after_named_rearm state.construction receipt.token receipt.incoming selected current stage incoming snapshot ambient ticket incomingCurrent selectedCurrent context.receiving
  have anchors : RetainedReplacementAnchors after.construction ambient.retained := by
    intro id destination found inactive supported
    exact context.retention.anchors id destination found inactive
      (replacementSupported_congr_destinations after.construction state.construction rfl id supported)
  have transportBoundaries : ∀ frames : OwnershipAmbient, OwnershipAmbientBoundaries state.construction frames →
      OwnershipAmbientBoundaries after.construction frames := by
    intro frames valid
    induction frames with
    | nil => trivial
    | cons frame outer ih =>
      refine ⟨?_, ih valid.2⟩
      intro index oldIncoming reserved selectedId oldSnapshot member found currentFound retained carried
      have old := waiting_update_active_preimage state.construction receipt.token receipt.incoming index .fresh oldIncoming reserved oldSnapshot found
      have oldCurrent := (destinationCurrent_congr_tables state.construction after.construction rfl rfl reserved).symm.trans currentFound
      exact valid.1 index oldIncoming reserved selectedId oldSnapshot member old oldCurrent retained carried
  have boundaries := transportBoundaries ambient context.retention.boundaries
  have reservations : OwnershipReservationFrames after.construction ambient := by
    intro index reservation found needed
    by_cases same : receipt.token = index
    · subst index
      have oldFrame := context.reservations receipt.token (.active (.named stage) incoming selected snapshot) ticket trivial
      exact oldFrame
    · have old : state.construction.exitReservations[index]? = some reservation := by
        simpa [after, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, same] using found
      exact context.reservations index reservation old needed
  exact ⟨source, ⟨source.structural.1, anchors, boundaries⟩, ⟨context.runtime.activations, context.runtime.breaks⟩,
    reservations, receiving, bounds, ⟨context.identities.activations, context.identities.breaks⟩⟩

theorem borrowed_named_step_accepted_world (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (initial state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (origin : Goose.Core.OriginId) (carriers : List Carrier) (receipt : BorrowedWaitingExitReservation)
    (stage : NamedReservationStage) (incoming selected current : Nat) (snapshot row : PendingDestination)
    (oldWorld : AcceptedWorld config initialized initial ambient types live regions pending)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (captured : receipt ∈ Goose.Proofs.ExitExecution.borrowedExitChannelReceipts activation initial)
    (ticket : state.construction.exitReservations[receipt.token]? = some (.active (.named stage) incoming selected snapshot))
    (incomingCurrent : destinationCurrent state.construction receipt.incoming = .ok current)
    (selectedCurrent : destinationCurrent state.construction selected = .ok current)
    (present : state.construction.destinations[current]? = some row)
    (unretained : (carriers.any fun carrier => match carrier with
      | .pendingNamed actual => actual == receipt.token | _ => false) = false) :
    ∃ after, Goose.Proofs.ExitExecution.borrowedExitChannelStep origin carriers receipt state = .ok (ForInStep.yield PUnit.unit) after ∧
      AcceptedWorld config initialized after ambient types live regions pending := by
  let updated := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! receipt.token (.waiting receipt.incoming) } }
  have step := borrowed_named_step origin carriers receipt state stage incoming selected current snapshot row ticket incomingCurrent present unretained
  have context := named_rearm_context state receipt stage incoming selected current snapshot row ambient ticket incomingCurrent selectedCurrent present world.ownership
  have separate := borrowed_receipts_pending_separate config initialized initial activation ambient types live regions pending oldWorld receipt captured
  have backed := rootedBacking_update_ticket config.layout state live receipt.token (.waiting receipt.incoming) world.backing
  have protections : ∀ region ∈ regions, ReceivingProtection config.layout updated live region := by
    intro region member
    exact receivingProtection_update_ticket config.layout state live region receipt.token (.waiting receipt.incoming) (world.protections region member)
  have frames := ticket_update_pending config.layout state receipt.token (.waiting receipt.incoming) pending world.carriers separate
  exact ⟨updated, step, ⟨⟨context, world.globals, world.globalTypes, world.layouts, world.typeFrontier, world.syntheticFrontier,
    world.heap, world.objectsRegistered, world.ordinalsRegistered, backed, protections, frames⟩, world.globalLive⟩⟩

#print axioms borrowed_named_step_accepted_world
#print axioms named_rearm_context
#print axioms channel_frames_after_named_rearm
#print axioms captured_frames_after_named_rearm

end Goose.Proofs.ConstructionAcceptedExecution

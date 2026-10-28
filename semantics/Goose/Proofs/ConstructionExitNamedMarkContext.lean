import Goose.Proofs.ConstructionExitNamedMarkFrame

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem named_mark_within (state : ConstructionState) (token incoming selected : Nat) (snapshot : PendingDestination)
    (outer : OwnershipAmbient) (receiving : Nat) (valid : OwnershipReceivingWithinSuccessorFrames state outer receiving) :
    OwnershipReceivingWithinSuccessorFrames { state with exitReservations := state.exitReservations.set! token (.active (.named .ready) incoming selected snapshot) } outer receiving := by
  intro frame member index owned source reserved oldSnapshot node ticket path ancestry
  have old := marked_named_fresh_preimage state token incoming selected snapshot index source reserved oldSnapshot ticket
  exact valid frame member index owned source reserved oldSnapshot node old
    (DestinationSuccessorPath.congr (before := { state with exitReservations := state.exitReservations.set! token (.active (.named .ready) incoming selected snapshot) }) (after := state) rfl path) ancestry

theorem channel_after_named_mark (state : ConstructionState) (token incoming selected : Nat) (snapshot next : PendingDestination)
    (outer : OwnershipAmbient) (channel : Channel)
    (ticket : state.exitReservations[token]? = some (.active (.named .awaitingSource) incoming selected snapshot))
    (valid : OwnershipChannelReceivingWithinFrames state outer channel) :
    OwnershipChannelReceivingWithinFrames { state with exitReservations := state.exitReservations.set! token (.active (.named .ready) incoming selected next) } outer channel := by
  let after := { state with exitReservations := state.exitReservations.set! token (.active (.named .ready) incoming selected next) }
  have currentBefore (id receiving : Nat) (found : destinationCurrent after id = .ok receiving) :
      destinationCurrent state id = .ok receiving := (destinationCurrent_congr_tables state after rfl rfl id).symm.trans found
  have inside : token < state.exitReservations.size := (Array.getElem?_eq_some_iff.mp ticket).1
  have newTicket : after.exitReservations[token]? = some (.active (.named .ready) incoming selected next) := by
    simp only [after, Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_self_of_lt inside
  cases channel with
  | register ty => trivial
  | construct id =>
    intro receiving found
    exact named_mark_within state token incoming selected next outer receiving (valid receiving (currentBefore id receiving found))
  | completion index =>
    constructor
    · intro oldIncoming found receiving currentFound
      by_cases same : token = index
      · subst index
        cases found.symm.trans newTicket
      · have old : state.exitReservations[index]? = some (.waiting oldIncoming) := by
          simpa [after, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, same] using found
        exact named_mark_within state token incoming selected next outer receiving
          (valid.1 oldIncoming old receiving (currentBefore oldIncoming receiving currentFound))
    · intro role oldIncoming oldSelected oldSnapshot found receiving currentFound
      by_cases same : token = index
      · subst index
        have equal := Option.some.inj (found.symm.trans newTicket)
        cases equal
        exact named_mark_within state token incoming selected next outer receiving
          (valid.2 (.named .awaitingSource) incoming selected snapshot ticket receiving (currentBefore selected receiving currentFound))
      · have old : state.exitReservations[index]? = some (.active role oldIncoming oldSelected oldSnapshot) := by
          simpa [after, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, same] using found
        exact named_mark_within state token incoming selected next outer receiving
          (valid.2 role oldIncoming oldSelected oldSnapshot old receiving (currentBefore oldSelected receiving currentFound))

theorem captured_after_named_mark (state : ConstructionState) (token incoming selected : Nat) (snapshot next : PendingDestination)
    (ambient : OwnershipAmbient) (ticket : state.exitReservations[token]? = some (.active (.named .awaitingSource) incoming selected snapshot))
    (frames : OwnershipCapturedReceivingFrames state ambient) (bounds : OwnershipCapturedReceivingBounds state ambient) :
    let after := { state with exitReservations := state.exitReservations.set! token (.active (.named .ready) incoming selected next) }
    OwnershipCapturedReceivingFrames after ambient ∧ OwnershipCapturedReceivingBounds after ambient := by
  let after := { state with exitReservations := state.exitReservations.set! token (.active (.named .ready) incoming selected next) }
  have inside : token < state.exitReservations.size := (Array.getElem?_eq_some_iff.mp ticket).1
  have boundChannel (channel : Channel) (valid : OwnershipChannelReceivingBound state channel) : OwnershipChannelReceivingBound after channel := by
    cases channel with
    | register ty => trivial
    | construct id => exact valid
    | completion index =>
      intro oldIncoming found
      by_cases same : token = index
      · subst index
        have newTicket : after.exitReservations[token]? = some (.active (.named .ready) incoming selected next) := by
          simp only [after, Array.set!_eq_setIfInBounds]
          exact Array.getElem?_setIfInBounds_self_of_lt inside
        cases found.symm.trans newTicket
      · have old : state.exitReservations[index]? = some (.waiting oldIncoming) := by
          simpa [after, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, same] using found
        exact valid oldIncoming old
  induction ambient with
  | nil => exact ⟨trivial, trivial⟩
  | cons frame outer ih =>
    obtain ⟨tailFrames, tailBounds⟩ := ih frames.2 bounds.2
    refine ⟨⟨?_, tailFrames⟩, ⟨?_, tailBounds⟩⟩
    · cases frame <;> try trivial
      case receivingScope capture carriers => exact channel_after_named_mark state token incoming selected snapshot next outer (.construct capture.incoming) ticket frames.1
      all_goals intro channel member; exact channel_after_named_mark state token incoming selected snapshot next outer channel ticket (frames.1 channel member)
    · cases frame <;> try trivial
      case receivingScope capture carriers => exact boundChannel (.construct capture.incoming) bounds.1
      all_goals intro channel member; exact boundChannel channel (bounds.1 channel member)

theorem mark_named_execution_context (state after : ExecutionState) (token incoming selected : Nat)
    (snapshot : PendingDestination) (ambient : OwnershipAmbient)
    (ticket : state.construction.exitReservations[token]? = some (.active (.named .awaitingSource) incoming selected snapshot))
    (marked : markNamedReservation token state.construction = .ok () after.construction)
    (runtime : after = { state with construction := after.construction })
    (context : OwnershipExecutionContext state ambient) : OwnershipExecutionContext after ambient := by
  obtain ⟨next, same⟩ := mark_named_exact_update state.construction after.construction token incoming selected snapshot ticket marked
  have source := mark_named_source_state state.construction after.construction token incoming selected snapshot ticket context.source marked
  have captured := captured_after_named_mark state.construction token incoming selected snapshot next ambient ticket context.receiving context.bounds
  let updated := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! token (.active (.named .ready) incoming selected next) } }
  have stateEq : after = updated := by rw [runtime, same]
  rw [stateEq] at source ⊢
  have anchors : RetainedReplacementAnchors updated.construction ambient.retained := by
    intro id destination found inactive supported
    exact context.retention.anchors id destination found inactive
      (replacementSupported_congr_destinations updated.construction state.construction rfl id supported)
  have transportBoundaries : ∀ frames : OwnershipAmbient, OwnershipAmbientBoundaries state.construction frames →
      OwnershipAmbientBoundaries updated.construction frames := by
    intro frames valid
    induction frames with
    | nil => trivial
    | cons frame outer ih =>
      refine ⟨?_, ih valid.2⟩
      intro index oldIncoming reserved selectedId oldSnapshot member found currentFound retained carried
      have old := marked_named_fresh_preimage state.construction token incoming selected next index oldIncoming reserved oldSnapshot found
      have oldCurrent := (destinationCurrent_congr_tables state.construction updated.construction rfl rfl reserved).symm.trans currentFound
      exact valid.1 index oldIncoming reserved selectedId oldSnapshot member old oldCurrent retained carried
  have reservations : OwnershipReservationFrames updated.construction ambient := by
    intro index reservation found needed
    by_cases equal : token = index
    · subst index
      exact context.reservations token (.active (.named .awaitingSource) incoming selected snapshot) ticket trivial
    · have old : state.construction.exitReservations[index]? = some reservation := by
        simpa [updated, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, equal] using found
      exact context.reservations index reservation old needed
  exact ⟨source, ⟨source.structural.1, anchors, transportBoundaries ambient context.retention.boundaries⟩,
    ⟨context.runtime.activations, context.runtime.breaks⟩, reservations, captured.1, captured.2,
    ⟨context.identities.activations, context.identities.breaks⟩⟩

theorem mark_named_accepted_world (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (initial state : ExecutionState) (after : ConstructionState)
    (token incoming selected : Nat) (snapshot : PendingDestination) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (oldWorld : AcceptedWorld config initialized initial ambient types live regions pending)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (receipt : BorrowedWaitingExitReservation) (captured : receipt ∈ borrowedExitChannelReceipts activation initial)
    (tokenEq : token = receipt.token)
    (ticket : state.construction.exitReservations[token]? = some (.active (.named .awaitingSource) incoming selected snapshot))
    (marked : markNamedReservation token state.construction = .ok () after) :
    AcceptedWorld config initialized { state with construction := after } ambient types live regions pending := by
  obtain ⟨next, same⟩ := mark_named_exact_update state.construction after token incoming selected snapshot ticket marked
  have separation : ∀ frame ∈ pending, .completion token ∉ frame.channels := by
    simpa only [tokenEq] using borrowed_receipts_pending_separate config initialized initial activation ambient types live regions pending oldWorld receipt captured
  have context := mark_named_execution_context state { state with construction := after } token incoming selected snapshot ambient ticket marked rfl world.ownership
  rw [same] at context ⊢
  have backed := rootedBacking_update_ticket config.layout state live token (.active (.named .ready) incoming selected next) world.backing
  have frames := ticket_update_pending config.layout state token (.active (.named .ready) incoming selected next) pending world.carriers separation
  have protections : ∀ region ∈ regions, ReceivingProtection config.layout { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token (.active (.named .ready) incoming selected next) } } live region := by
    intro region member
    exact receivingProtection_update_ticket config.layout state live region token (.active (.named .ready) incoming selected next) (world.protections region member)
  exact ⟨⟨context, world.globals, world.globalTypes, world.layouts, world.typeFrontier, world.syntheticFrontier,
    world.heap, world.objectsRegistered, world.ordinalsRegistered, backed, protections, frames⟩, world.globalLive⟩

theorem borrowed_named_mark_rearm_accepted_world (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (initial state : ExecutionState) (after : ConstructionState)
    (receipt : BorrowedWaitingExitReservation) (snapshot row : PendingDestination) (current : Nat)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (origin : Goose.Core.OriginId) (carriers : List Carrier)
    (oldWorld : AcceptedWorld config initialized initial ambient types live regions pending)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (captured : receipt ∈ borrowedExitChannelReceipts activation initial)
    (ticket : state.construction.exitReservations[receipt.token]? = some (.active (.named .awaitingSource) receipt.incoming receipt.incoming snapshot))
    (marked : markNamedReservation receipt.token state.construction = .ok () after)
    (resolved : destinationCurrent state.construction receipt.incoming = .ok current)
    (present : state.construction.destinations[current]? = some row)
    (unretained : (carriers.any fun carrier => match carrier with
      | .pendingNamed actual => actual == receipt.token | _ => false) = false) :
    let built := { state with construction := after }
    liftConstruction origin (markNamedReservation receipt.token) state = .ok () built ∧
    AcceptedWorld config initialized built ambient types live regions pending ∧
    ∃ final, borrowedExitChannelStep origin carriers receipt built = .ok (ForInStep.yield PUnit.unit) final ∧
      AcceptedWorld config initialized final ambient types live regions pending := by
  let built := { state with construction := after }
  have markedWorld := mark_named_accepted_world config initialized activation initial state after receipt.token receipt.incoming receipt.incoming snapshot ambient types live regions pending oldWorld world receipt captured rfl ticket marked
  obtain ⟨next, same⟩ := mark_named_exact_update state.construction after receipt.token receipt.incoming receipt.incoming snapshot ticket marked
  have resolvedAfter : destinationCurrent after receipt.incoming = .ok current := by
    rw [same]
    exact (destinationCurrent_congr_tables state.construction
      { state.construction with exitReservations := state.construction.exitReservations.set! receipt.token (.active (.named .ready) receipt.incoming receipt.incoming next) } rfl rfl receipt.incoming).trans resolved
  have presentAfter : after.destinations[current]? = some row := by simpa only [same] using present
  have final := marked_borrowed_rearm_world config initialized activation initial state built ambient types live regions pending origin carriers receipt snapshot row current
    oldWorld markedWorld captured ticket marked resolvedAfter presentAfter unretained
  refine ⟨?_, markedWorld, final⟩
  simp only [liftConstruction, marked]

#print axioms borrowed_named_mark_rearm_accepted_world
#print axioms mark_named_accepted_world
#print axioms mark_named_execution_context
#print axioms captured_after_named_mark

end Goose.Proofs.ConstructionAcceptedExecution

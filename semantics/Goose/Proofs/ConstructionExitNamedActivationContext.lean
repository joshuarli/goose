import Goose.Proofs.ConstructionExitNamedAliasSelection

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem named_activation_within (state : ConstructionState) (token incoming : Nat) (snapshot : PendingDestination)
    (outer : OwnershipAmbient) (receiving : Nat) (valid : OwnershipReceivingWithinSuccessorFrames state outer receiving) :
    OwnershipReceivingWithinSuccessorFrames { state with exitReservations := state.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) } outer receiving := by
  intro frame member index owned source selected oldSnapshot node ticket path ancestry
  have old := named_activation_fresh_preimage state token incoming snapshot index source selected oldSnapshot ticket
  exact valid frame member index owned source selected oldSnapshot node old
    (DestinationSuccessorPath.congr (before := { state with exitReservations := state.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) }) (after := state) rfl path) ancestry

theorem channel_after_named_activation (state : ConstructionState) (token incoming : Nat) (snapshot : PendingDestination)
    (outer : OwnershipAmbient) (channel : Channel)
    (waiting : state.exitReservations[token]? = some (.waiting incoming))
    (valid : OwnershipChannelReceivingWithinFrames state outer channel) :
    OwnershipChannelReceivingWithinFrames { state with exitReservations := state.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) } outer channel := by
  let after := { state with exitReservations := state.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) }
  have currentBefore (id receiving : Nat) (found : destinationCurrent after id = .ok receiving) :
      destinationCurrent state id = .ok receiving := (destinationCurrent_congr_tables state after rfl rfl id).symm.trans found
  have indexInside : token < state.exitReservations.size := (Array.getElem?_eq_some_iff.mp waiting).1
  have newTicket : after.exitReservations[token]? = some (.active (.named .awaitingSource) incoming incoming snapshot) := by
    simp only [after, Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_self_of_lt indexInside
  cases channel with
  | register ty => trivial
  | construct id =>
    intro receiving found
    exact named_activation_within state token incoming snapshot outer receiving (valid receiving (currentBefore id receiving found))
  | completion index =>
    constructor
    · intro oldIncoming found receiving currentFound
      by_cases same : token = index
      · subst index
        cases found.symm.trans newTicket
      · have old : state.exitReservations[index]? = some (.waiting oldIncoming) := by
          simpa [after, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, same] using found
        exact named_activation_within state token incoming snapshot outer receiving
          (valid.1 oldIncoming old receiving (currentBefore oldIncoming receiving currentFound))
    · intro role oldIncoming oldSelected oldSnapshot found receiving currentFound
      by_cases same : token = index
      · subst index
        have equal := Option.some.inj (found.symm.trans newTicket)
        cases equal
        exact named_activation_within state token incoming snapshot outer receiving
          (valid.1 incoming waiting receiving (currentBefore incoming receiving currentFound))
      · have old : state.exitReservations[index]? = some (.active role oldIncoming oldSelected oldSnapshot) := by
          simpa [after, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, same] using found
        exact named_activation_within state token incoming snapshot outer receiving
          (valid.2 role oldIncoming oldSelected oldSnapshot old receiving (currentBefore oldSelected receiving currentFound))

theorem captured_after_named_activation (state : ConstructionState) (token incoming : Nat) (snapshot : PendingDestination)
    (ambient : OwnershipAmbient) (waiting : state.exitReservations[token]? = some (.waiting incoming))
    (frames : OwnershipCapturedReceivingFrames state ambient) (bounds : OwnershipCapturedReceivingBounds state ambient) :
    let after := { state with exitReservations := state.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) }
    OwnershipCapturedReceivingFrames after ambient ∧ OwnershipCapturedReceivingBounds after ambient := by
  let after := { state with exitReservations := state.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) }
  have inside : token < state.exitReservations.size := (Array.getElem?_eq_some_iff.mp waiting).1
  have boundChannel (channel : Channel) (valid : OwnershipChannelReceivingBound state channel) : OwnershipChannelReceivingBound after channel := by
    cases channel with
    | register ty => trivial
    | construct id => exact valid
    | completion index =>
      intro oldIncoming found
      by_cases same : token = index
      · subst index
        have newTicket : after.exitReservations[token]? = some (.active (.named .awaitingSource) incoming incoming snapshot) := by
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
      case receivingScope capture carriers => exact channel_after_named_activation state token incoming snapshot outer (.construct capture.incoming) waiting frames.1
      all_goals intro channel member; exact channel_after_named_activation state token incoming snapshot outer channel waiting (frames.1 channel member)
    · cases frame <;> try trivial
      case receivingScope capture carriers => exact boundChannel (.construct capture.incoming) bounds.1
      all_goals intro channel member; exact boundChannel channel (bounds.1 channel member)

theorem named_open_activation_context (state : ExecutionState) (token incoming : Nat) (snapshot : PendingDestination)
    (ambient : OwnershipAmbient) (waiting : state.construction.exitReservations[token]? = some (.waiting incoming))
    (present : state.construction.destinations[incoming]? = some snapshot) (opened : snapshot.progress = .open 0)
    (current : destinationCurrent state.construction incoming = .ok incoming)
    (context : OwnershipExecutionContext state ambient) :
    OwnershipExecutionContext { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) } } ambient := by
  let after := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) } }
  have source := named_open_activation_source state.construction token incoming snapshot waiting present opened current context.source
  have captured := captured_after_named_activation state.construction token incoming snapshot ambient waiting context.receiving context.bounds
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
      intro index oldIncoming reserved selected oldSnapshot member found currentFound retained carried
      have old := named_activation_fresh_preimage state.construction token incoming snapshot index oldIncoming reserved oldSnapshot found
      have oldCurrent := (destinationCurrent_congr_tables state.construction after.construction rfl rfl reserved).symm.trans currentFound
      exact valid.1 index oldIncoming reserved selected oldSnapshot member old oldCurrent retained carried
  have reservations : OwnershipReservationFrames after.construction ambient := by
    intro index reservation found needed
    by_cases same : token = index
    · subst index
      exact context.reservations token (.waiting incoming) waiting trivial
    · have old : state.construction.exitReservations[index]? = some reservation := by
        simpa [after, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, same] using found
      exact context.reservations index reservation old needed
  exact ⟨source, ⟨source.structural.1, anchors, transportBoundaries ambient context.retention.boundaries⟩,
    ⟨context.runtime.activations, context.runtime.breaks⟩, reservations, captured.1, captured.2,
    ⟨context.identities.activations, context.identities.breaks⟩⟩

theorem named_open_activation_world (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (token incoming : Nat) (snapshot : PendingDestination) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (waiting : state.construction.exitReservations[token]? = some (.waiting incoming))
    (present : state.construction.destinations[incoming]? = some snapshot) (opened : snapshot.progress = .open 0)
    (current : destinationCurrent state.construction incoming = .ok incoming)
    (world : AcceptedWorld config initialized state ambient types live regions pending) :
    AcceptedWorld config initialized { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) } }
      ambient types live regions pending := by
  let replacement : ExitReservation := .active (.named .awaitingSource) incoming incoming snapshot
  let after := { state with construction := { state.construction with exitReservations := state.construction.exitReservations.set! token replacement } }
  have separate : ∀ frame ∈ pending, .completion token ∉ frame.channels := by
    intro frame member
    exact waiting_ticket_absent_from_ready state token incoming frame.channels frame.carriers waiting (world.carriers frame member).1
  have context := named_open_activation_context state token incoming snapshot ambient waiting present opened current world.ownership
  have backing := rootedBacking_update_ticket config.layout state live token replacement world.backing
  have protections : ∀ region ∈ regions, ReceivingProtection config.layout after live region := by
    intro region member
    exact receivingProtection_update_ticket config.layout state live region token replacement (world.protections region member)
  have frames := ticket_update_pending config.layout state token replacement pending world.carriers separate
  exact ⟨⟨context, world.globals, world.globalTypes, world.layouts, world.typeFrontier, world.syntheticFrontier,
    world.heap, world.objectsRegistered, world.ordinalsRegistered, backing, protections, frames⟩, world.globalLive⟩

theorem borrowed_alias_activation_rearm_world (config : EvalConfig) (initialized : Nat)
    (source activation : RuntimeActivation) (initial : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (origin : Goose.Core.OriginId) (carriers : List Carrier) (receipt : BorrowedWaitingExitReservation)
    (snapshot : PendingDestination) (localVar : Goose.Core.VarId) (root : Goose.Core.RootInst) (stored : StoredValue)
    (world : AcceptedWorld config initialized initial ambient types live regions pending)
    (captured : receipt ∈ borrowedExitChannelReceipts activation initial)
    (present : initial.construction.destinations[receipt.incoming]? = some snapshot)
    (opened : snapshot.progress = .open 0)
    (current : destinationCurrent initial.construction receipt.incoming = .ok receipt.incoming)
    (rooted : rootOf source localVar initial = .ok root initial)
    (value : initial.objects.lookup root = some (.stored stored)) (alias : stored.destination = some receipt.incoming)
    (unretained : (carriers.any fun carrier => match carrier with
      | .pendingNamed actual => actual == receipt.token | _ => false) = false) :
    let activated := { initial with construction := { initial.construction with
      exitReservations := initial.construction.exitReservations.set! receipt.token
        (.active (.named .awaitingSource) receipt.incoming receipt.incoming snapshot) } }
    selectCompletionChannel source (.resultLocal localVar origin) (.completion receipt.token) initial = .ok (.construct receipt.incoming) activated ∧
    AcceptedWorld config initialized activated ambient types live regions pending ∧
    ∃ after, borrowedExitChannelStep origin carriers receipt activated = .ok (ForInStep.yield PUnit.unit) after ∧
      AcceptedWorld config initialized after ambient types live regions pending := by
  obtain ⟨channel, channelMember, capturedReceipt⟩ := List.mem_filterMap.mp captured
  cases channel with
  | register ty => cases capturedReceipt
  | construct id => cases capturedReceipt
  | completion token =>
    have capturedData := captureWaitingExitReservation_source token initial.construction receipt capturedReceipt
    have waiting : initial.construction.exitReservations[receipt.token]? = some (.waiting receipt.incoming) := by
      simpa only [capturedData.1] using capturedData.2
    let activated := { initial with construction := { initial.construction with
      exitReservations := initial.construction.exitReservations.set! receipt.token
        (.active (.named .awaitingSource) receipt.incoming receipt.incoming snapshot) } }
    have activeWorld := named_open_activation_world config initialized initial receipt.token receipt.incoming snapshot ambient types live regions pending waiting present opened current world
    have selection := selectCompletion_named_local_alias source initial receipt.token receipt.incoming snapshot localVar origin root stored waiting present opened current rooted value alias
    obtain ⟨_, after, step, finalWorld⟩ := borrowed_named_direct_activation_rearm config initialized activation initial ambient types live regions pending origin carriers receipt snapshot world captured present opened current unretained activeWorld
    exact ⟨selection, activeWorld, after, step, finalWorld⟩

#print axioms borrowed_alias_activation_rearm_world
#print axioms named_open_activation_context
#print axioms named_open_activation_world
#print axioms captured_after_named_activation

end Goose.Proofs.ConstructionAcceptedExecution

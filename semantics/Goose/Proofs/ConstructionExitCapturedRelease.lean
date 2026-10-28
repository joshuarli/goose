import Goose.Proofs.ConstructionExecutionOwnershipEvaluationReceivingFrames
import Goose.Proofs.ConstructionExitFrameRelease
import Goose.Proofs.ConstructionExitByteCaptured

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionAcceptedExecution

private theorem live_ticket_before_release (state : ConstructionState) (released token : Nat)
    (reservation : ExitReservation) (live : OwnershipReservationNeedsFrame reservation)
    (present : (state.exitReservations.set! released .released)[token]? = some reservation) :
    state.exitReservations[token]? = some reservation := by
  by_cases same : token = released
  · subst token
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    have releasedTicket : (state.exitReservations.set! released .released)[released]? = some .released := by
      rw [Array.set!_eq_setIfInBounds] at present ⊢
      exact Array.getElem?_setIfInBounds_self_of_lt (by simpa using inside)
    have equal := Option.some.inj (present.symm.trans releasedTicket)
    subst reservation
    exact False.elim live
  · simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Ne.symm same] using present

private theorem within_after_release (state : ConstructionState) (released : Nat) (outer : OwnershipAmbient)
    (receiving : Nat) (valid : OwnershipReceivingWithinSuccessorFrames state outer receiving) :
    OwnershipReceivingWithinSuccessorFrames { state with exitReservations := state.exitReservations.set! released .released } outer receiving := by
  intro frame member token owned incoming reserved snapshot node ticket aliases ancestry
  have old := live_ticket_before_release state released token (.active .fresh incoming reserved snapshot) trivial ticket
  exact valid frame member token owned incoming reserved snapshot node old (DestinationSuccessorPath.congr (before := { state with exitReservations := state.exitReservations.set! released .released }) (after := state) rfl aliases) ancestry

private theorem channel_after_release (state : ConstructionState) (released : Nat) (outer : OwnershipAmbient)
    (channel : Channel) (valid : OwnershipChannelReceivingWithinFrames state outer channel) :
    OwnershipChannelReceivingWithinFrames { state with exitReservations := state.exitReservations.set! released .released } outer channel := by
  have currentBefore (id receiving : Nat)
      (current : destinationCurrent { state with exitReservations := state.exitReservations.set! released .released } id = .ok receiving) :
      destinationCurrent state id = .ok receiving := by
    rw [destinationCurrent_congr_tables state
      { state with exitReservations := state.exitReservations.set! released .released } rfl rfl id] at current
    exact current
  cases channel with
  | register ty => trivial
  | construct incoming =>
    intro receiving current
    exact within_after_release state released outer receiving (valid receiving (currentBefore incoming receiving current))
  | completion token =>
    constructor
    · intro incoming ticket receiving current
      have old := live_ticket_before_release state released token (.waiting incoming) trivial ticket
      exact within_after_release state released outer receiving (valid.1 incoming old receiving (currentBefore incoming receiving current))
    · intro role incoming selected snapshot ticket receiving current
      have old := live_ticket_before_release state released token (.active role incoming selected snapshot) trivial ticket
      exact within_after_release state released outer receiving (valid.2 role incoming selected snapshot old receiving (currentBefore selected receiving current))

private theorem bound_after_release (state : ConstructionState) (released : Nat) (channel : Channel)
    (valid : OwnershipChannelReceivingBound state channel) :
    OwnershipChannelReceivingBound { state with exitReservations := state.exitReservations.set! released .released } channel := by
  cases channel with
  | register ty => trivial
  | construct incoming => exact valid
  | completion token =>
    intro incoming ticket
    exact valid incoming (live_ticket_before_release state released token (.waiting incoming) trivial ticket)

theorem captured_receiving_after_release (state : ConstructionState) (released : Nat) (ambient : OwnershipAmbient)
    (bounds : OwnershipCapturedReceivingBounds state ambient) (frames : OwnershipCapturedReceivingFrames state ambient) :
    OwnershipCapturedReceivingBounds { state with exitReservations := state.exitReservations.set! released .released } ambient ∧
    OwnershipCapturedReceivingFrames { state with exitReservations := state.exitReservations.set! released .released } ambient := by
  induction ambient with
  | nil => exact ⟨True.intro, True.intro⟩
  | cons frame outer ih =>
    obtain ⟨outerBounds, outerFrames⟩ := ih bounds.2 frames.2
    have headBound : OwnershipFrameReceivingBound { state with exitReservations := state.exitReservations.set! released .released } frame := by
      cases frame <;> try trivial
      case receivingScope capture carriers =>
        exact bound_after_release state released (.construct capture.incoming) (by simpa only [OwnershipFrameReceivingBound] using bounds.1)
      all_goals intro channel member; exact bound_after_release state released channel (bounds.1 channel member)
    have headFrame : OwnershipFrameReceivingWithinFrames { state with exitReservations := state.exitReservations.set! released .released } outer frame := by
      cases frame <;> try trivial
      case receivingScope capture carriers =>
        exact channel_after_release state released outer (.construct capture.incoming) (by simpa only [OwnershipFrameReceivingWithinFrames] using frames.1)
      all_goals intro channel member; exact channel_after_release state released outer channel (frames.1 channel member)
    exact ⟨⟨headBound, outerBounds⟩, ⟨headFrame, outerFrames⟩⟩

theorem cleanup_captured_receiving_outer (state : ExecutionState) (token incoming selected : Nat)
    (snapshot : PendingDestination) (channels : List Channel) (carriers : List Carrier)
    (outer : OwnershipAmbient) (origin : Goose.Core.OriginId)
    (environment : RuntimeActivation) (scope : Nat) (scopeInst : Goose.Core.ScopeInst)
    (ticket : state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (bounds : OwnershipCapturedReceivingBounds state.construction (.exitChannels [token] channels carriers :: outer))
    (receiving : OwnershipCapturedReceivingFrames state.construction (.exitChannels [token] channels carriers :: outer))
    (frames : OwnershipReservationFrames state.construction (.exitChannels [token] channels carriers :: outer)) :
    ∃ cleaned,
      Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed origin [] [token] false carriers state = .ok () cleaned ∧
      OwnershipCapturedReceivingBounds (releaseScopeState environment scope scopeInst cleaned).construction outer ∧
      OwnershipCapturedReceivingFrames (releaseScopeState environment scope scopeInst cleaned).construction outer ∧
      OwnershipReservationFrames (releaseScopeState environment scope scopeInst cleaned).construction outer := by
  obtain ⟨cleaned, cleanup, _, remaining⟩ :=
    cleanup_single_exit_frame state token incoming selected snapshot channels carriers outer origin ticket frames
  have released := releaseExitReservation_active state.construction token .fresh incoming selected snapshot ticket
  have actual : Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed origin [] [token] false carriers state =
      .ok () { state with construction := { state.construction with
        exitReservations := state.construction.exitReservations.set! token .released } } := by
    simp only [Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.forIn_cons, List.forIn_nil,
      liftConstruction, released, bind, pure]
  have same := cleanup.symm.trans actual
  cases same
  have captured := captured_receiving_after_release state.construction token outer bounds.2 receiving.2
  exact ⟨_, actual, captured.1, captured.2, remaining⟩


theorem byte_build_cleanup_captured_outer (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id count token incoming : Nat) (snapshot : PendingDestination)
    (bytes : List UInt8) (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (channels : List Channel) (carriers : List Carrier) (outer : OwnershipAmbient)
    (valid : OwnershipSourceState before.construction)
    (bounds : OwnershipCapturedReceivingBounds before.construction (.exitChannels [token] channels carriers :: outer))
    (receiving : OwnershipCapturedReceivingFrames before.construction (.exitChannels [token] channels carriers :: outer))
    (frames : OwnershipReservationFrames before.construction (.exitChannels [token] channels carriers :: outer))
    (ticket : before.construction.exitReservations[token]? = some (.active .fresh incoming id snapshot))
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after)
    (scope : Nat) (scopeInst : Goose.Core.ScopeInst) :
    ∃ cleaned,
      Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed origin [] [token] false carriers after = .ok () cleaned ∧
      OwnershipCapturedReceivingBounds (releaseScopeState environment scope scopeInst cleaned).construction outer ∧
      OwnershipCapturedReceivingFrames (releaseScopeState environment scope scopeInst cleaned).construction outer ∧
      OwnershipReservationFrames (releaseScopeState environment scope scopeInst cleaned).construction outer := by
  have captured := build_packed_bytes_captured_receiving fuel config environment id count bytes origin before after
    (.exitChannels [token] channels carriers :: outer) valid bounds receiving ready packed request current executed
  have tickets := buildExpr_bytes_tickets fuel config environment id (.varr (.int .u8)) bytes origin before after
    ready.destination count valid current ready.present ready.opened executed
  have afterTicket : after.construction.exitReservations[token]? = some (.active .fresh incoming id snapshot) := by
    simpa only [tickets] using ticket
  have afterFrames : OwnershipReservationFrames after.construction (.exitChannels [token] channels carriers :: outer) := by
    simpa only [OwnershipReservationFrames, tickets] using frames
  exact cleanup_captured_receiving_outer after token incoming id snapshot channels carriers outer origin environment scope scopeInst
    afterTicket captured.1 captured.2 afterFrames

#print axioms byte_build_cleanup_captured_outer

#print axioms cleanup_captured_receiving_outer
#print axioms captured_receiving_after_release

end Goose.Proofs.ConstructionExecutionOwnership

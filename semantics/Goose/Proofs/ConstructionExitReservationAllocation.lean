import Goose.Proofs.ConstructionExitReservationContext
import Goose.Proofs.ConstructionExitOpenReservation
import Goose.Proofs.ConstructionExecutionOwnershipSourceAllocation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem captured_bounds_push_active (state : ConstructionState) (ambient : OwnershipAmbient)
    (role : ExitReservationRole) (incoming selected : Nat) (snapshot : PendingDestination)
    (valid : OwnershipCapturedReceivingBounds state ambient) :
    OwnershipCapturedReceivingBounds { state with exitReservations := state.exitReservations.push (.active role incoming selected snapshot) } ambient := by
  have channelBound (channel : Channel) (bound : OwnershipChannelReceivingBound state channel) :
      OwnershipChannelReceivingBound { state with exitReservations := state.exitReservations.push (.active role incoming selected snapshot) } channel := by
    cases channel with
    | register ty => trivial
    | construct id => exact bound
    | completion token =>
      intro id ticket
      by_cases fresh : token = state.exitReservations.size
      · simp [Array.getElem?_push, fresh] at ticket
      · apply bound id
        simpa [Array.getElem?_push, fresh] using ticket
  induction ambient with
  | nil => trivial
  | cons frame rest ih =>
    refine ⟨?_, ih valid.2⟩
    cases frame <;> try trivial
    case receivingScope capture carriers => exact channelBound (.construct capture.incoming) valid.1
    all_goals intro channel member; exact channelBound channel (valid.1 channel member)

theorem accepted_open_reservation_allocation (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (row : PendingDestination) (present : before.construction.destinations[incoming]? = some row)
    (opened : row.progress = .open (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (channels : List Channel) (carriers : List Goose.Construct.Carrier)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved) :
    ∃ allocated,
      openExitReplacement incoming before.construction = .ok selected allocated ∧
      reserved = { allocated with exitReservations := allocated.exitReservations.push (.active .fresh incoming selected row) } ∧
      OwnershipSourceState allocated ∧ OwnershipCapturedReceivingBounds reserved (.exitChannels [token] channels carriers :: ambient) ∧
      OwnershipCapturedReceivingFrames allocated ambient := by
  have renewal : renewReceivingDestination incoming before.construction = .ok incoming before.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, present, opened]
  have frontier : exitFrontierAction (before.construction.destinations.size + 1) incoming before.construction =
      .ok incoming before.construction :=
    exitFrontier_open before.construction.destinations.size incoming (count + 1) before.construction row present opened
  rw [reserveExitDestination_equation] at reservation
  simp only [show (ExitSource.newValue == ExitSource.namedResult) = false from rfl,
    Bool.false_eq_true, ↓reduceIte, renewal, bind, ConstructionM.get, frontier,
    reserveLookupStep, lookupDestination_result, present, opened, Bool.false_or] at reservation
  cases replacement : openExitReplacement incoming before.construction with
  | fault reason state => simp only [replacement] at reservation; cases reservation
  | ok picked allocated =>
    simp only [replacement, ConstructionM.get, ConstructionM.set, bind, pure, ConstructionResult.ok.injEq] at reservation
    obtain ⟨samePair, rfl⟩ := reservation
    cases samePair
    have extension := openExitReplacement_ownership_source incoming before.construction world.ownership.source.structural.1.1.1
    have source := constructionPrimitive_sourceState_of_sourceExtension (openExitReplacement incoming)
      (.openExitReplacement incoming) before.construction world.ownership.source extension
    have captured := constructionPrimitive_capturedReceiving_of_sourceExtension (openExitReplacement incoming)
      (.openExitReplacement incoming) before.construction world.ownership.source ambient
      world.ownership.bounds world.ownership.receiving extension
    rw [replacement] at source captured
    exact ⟨allocated, rfl, rfl, source,
      ⟨trivial, captured_bounds_push_active allocated ambient .fresh incoming selected row captured.1⟩, captured.2⟩

#print axioms accepted_open_reservation_allocation
#print axioms captured_bounds_push_active

end Goose.Proofs.ConstructionAcceptedExecution

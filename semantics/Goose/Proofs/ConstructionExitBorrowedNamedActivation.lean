import Goose.Proofs.ConstructionExitBorrowedFrames
import Goose.Proofs.ConstructionExitCompletionActivation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem selectWaiting_named_open_direct (state : ConstructionState) (token incoming : Nat)
    (snapshot : PendingDestination)
    (waiting : state.exitReservations[token]? = some (.waiting incoming))
    (present : state.destinations[incoming]? = some snapshot) (opened : snapshot.progress = .open 0)
    (current : destinationCurrent state incoming = .ok incoming) :
    selectWaitingExitDestination token .namedResult state = .ok incoming { state with
      exitReservations := state.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) } := by
  have renewal : renewReceivingDestination incoming state = .ok incoming state := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, present, opened]
  simp only [selectWaitingExitDestination, ConstructionM.get, waiting, bind, prepareExitDestination_equation,
    show (ExitSource.namedResult == ExitSource.namedResult) = true from rfl, ↓reduceIte,
    renewal, lookupDestination_result, present, opened, Bool.true_or, pure, ConstructionM.set]

theorem borrowed_named_direct_activation_rearm (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (initial : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (origin : OriginId) (carriers : List Carrier) (receipt : BorrowedWaitingExitReservation)
    (snapshot : PendingDestination)
    (oldWorld : AcceptedWorld config initialized initial ambient types live regions pending)
    (captured : receipt ∈ borrowedExitChannelReceipts activation initial)
    (present : initial.construction.destinations[receipt.incoming]? = some snapshot)
    (opened : snapshot.progress = .open 0)
    (current : destinationCurrent initial.construction receipt.incoming = .ok receipt.incoming)
    (unretained : (carriers.any fun carrier => match carrier with
      | .pendingNamed actual => actual == receipt.token | _ => false) = false)
    (activeWorld : AcceptedWorld config initialized { initial with construction := { initial.construction with
      exitReservations := initial.construction.exitReservations.set! receipt.token
        (.active (.named .awaitingSource) receipt.incoming receipt.incoming snapshot) } } ambient types live regions pending) :
    let activated := { initial with construction := { initial.construction with
      exitReservations := initial.construction.exitReservations.set! receipt.token
        (.active (.named .awaitingSource) receipt.incoming receipt.incoming snapshot) } }
    selectWaitingExitDestination receipt.token .namedResult initial.construction = .ok receipt.incoming activated.construction ∧
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
    have selected := selectWaiting_named_open_direct initial.construction receipt.token receipt.incoming snapshot waiting present opened current
    have inside := (Array.getElem?_eq_some_iff.mp waiting).1
    have activeTicket : activated.construction.exitReservations[receipt.token]? = some (.active (.named .awaitingSource) receipt.incoming receipt.incoming snapshot) := by
      simp [activated, Array.set!_eq_setIfInBounds, inside]
    have activeCurrent : destinationCurrent activated.construction receipt.incoming = .ok receipt.incoming := by
      exact (destinationCurrent_congr_tables initial.construction activated.construction rfl rfl receipt.incoming).trans current
    exact ⟨selected, borrowed_named_step_accepted_world config initialized activation initial activated ambient types live regions pending
      origin carriers receipt .awaitingSource receipt.incoming receipt.incoming receipt.incoming snapshot snapshot oldWorld activeWorld captured
      activeTicket activeCurrent activeCurrent present unretained⟩

#print axioms selectWaiting_named_open_direct
#print axioms borrowed_named_direct_activation_rearm

end Goose.Proofs.ConstructionAcceptedExecution

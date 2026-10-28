import Goose.Proofs.ExitExecutionLiveCarrierLanding

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership

theorem CompletedCarrierLandingFrame.receiverStorage (layout : LayoutEnv) (state after : ExecutionState)
    (ambient : OwnershipAmbient) (incoming source : Nat)
    (context : OwnershipExecutionContext state ambient)
    (backed : CarrierResultBacking layout state (.completed source))
    (ready : ReceivingCarrierLandingReady state incoming source)
    (landing : CompletedCarrierLandingFrame state incoming source after) :
    ∃ row, after.construction.destinations[source]? = some row ∧
      row.backing.receiverStorage = ready.receivingDestination.backing.receiverStorage := by
  cases backed with
  | completed id count replacement stored present built sampled backing =>
    have supported : ReplacementSupported state.construction source :=
      .active source replacement present (by simp only [built, activeProgress])
    have sameBacking := ready.path.backing context.source.structural.1.2.2.1
      ready.receivingDestination replacement ready.receivingPresent present supported
    cases landing with
    | current resolved => exact ⟨replacement, present, congrArg DestinationBacking.receiverStorage sameBacking⟩
    | commit receiving count current anchor storage parentUpdate chain resolved currentPresent currentBuilt
        anchorPresent storagePresent sameStorage ordered inside parentBound parentDifferent parentFootprint =>
      have sameReceiver : receiving = ready.receiving := Except.ok.inj (resolved.symm.trans ready.resolved)
      subst receiving
      have sameAnchor : anchor = ready.receivingDestination := Option.some.inj (anchorPresent.symm.trans ready.receivingPresent)
      subst anchor
      have sameCurrent : current = replacement := Option.some.inj (currentPresent.symm.trans present)
      subst current
      refine ⟨landedReplacementRow replacement ready.receivingDestination count, ?_, ?_⟩
      · exact completedLandingState_replacement state.construction source ready.receiving count replacement
          ready.receivingDestination storage parentUpdate (Array.getElem?_eq_some_iff.mp present).1 parentDifferent
      · exact congrArg DestinationBacking.receiverStorage sameBacking

theorem landCarriersInto_construct_receiverStorage (layout : LayoutEnv) (origin : OriginId)
    (state : ExecutionState) (ambient : OwnershipAmbient) (incoming source : Nat)
    (context : OwnershipExecutionContext state ambient)
    (backed : CarrierResultBacking layout state (.completed source))
    (ready : ReceivingCarrierLandingReady state incoming source) :
    ∃ after row, landCarriersInto origin [.construct incoming] [.completed source] state = .ok () after ∧
      after.construction.destinations[source]? = some row ∧
      row.backing.receiverStorage = ready.receivingDestination.backing.receiverStorage := by
  obtain ⟨after, landed, nextBacking, ⟨nextReady⟩, tickets, frame⟩ :=
    landCarriersInto_construct_completed layout origin state ambient incoming source context backed ready
  obtain ⟨row, present, storage⟩ := frame.receiverStorage layout state after ambient incoming source context backed ready
  exact ⟨after, row, landed, present, storage⟩

#print axioms CompletedCarrierLandingFrame.receiverStorage
#print axioms landCarriersInto_construct_receiverStorage

end Goose.Proofs.ExitExecution

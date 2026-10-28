import Goose.Proofs.ExitExecutionLiveCarrierLanding
import Goose.Proofs.ConstructionExitByteNormalize

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem CompletedCarrierLandingFrame.replacement_receiver_metadata
    (before after : ExecutionState) (incoming source count : Nat)
    (receiver replacement : PendingDestination)
    (resolved : destinationCurrent before.construction incoming = .ok incoming)
    (different : incoming ≠ source)
    (receiverPresent : before.construction.destinations[incoming]? = some receiver)
    (receiverRole : receiver.use = .receiver)
    (sourcePresent : before.construction.destinations[source]? = some replacement)
    (sourceBuilt : replacement.progress = .built count)
    (frame : CompletedCarrierLandingFrame before incoming source after) :
    ∃ row, after.construction.destinations[source]? = some row ∧
      row.use = .receiver ∧ row.adaptation = replacement.adaptation ∧
      row.capability.layout = replacement.capability.layout ∧
      row.capability.logicalType = replacement.capability.logicalType ∧ row.progress = .built count := by
  cases frame with
  | current currentResolved =>
    have same : incoming = source := Except.ok.inj (resolved.symm.trans currentResolved)
    exact False.elim (different same)
  | commit receiving builtCount current anchor storage parentUpdate chain currentResolved currentPresent currentBuilt anchorPresent
      stored sameStorage ordered inside parentBound parentDifferent parentFootprint =>
    have sameReceiver : receiving = incoming := Except.ok.inj (currentResolved.symm.trans resolved)
    subst receiving
    have sameAnchor : anchor = receiver := Option.some.inj (anchorPresent.symm.trans receiverPresent)
    subst anchor
    have sameCurrent : current = replacement := Option.some.inj (currentPresent.symm.trans sourcePresent)
    subst current
    have sameCount : builtCount = count := DestinationProgress.built.inj (currentBuilt.symm.trans sourceBuilt)
    subst builtCount
    refine ⟨landedReplacementRow replacement receiver count, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · exact completedLandingState_replacement before.construction source incoming count replacement receiver storage parentUpdate
        (Array.getElem?_eq_some_iff.mp sourcePresent).1 parentDifferent
    · exact receiverRole

theorem land_constructed_byte_finishes (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (incoming source count : Nat)
    (receiver replacement : PendingDestination)
    (context : OwnershipExecutionContext before ambient)
    (backed : CarrierResultBacking layout before (.completed source))
    (ready : ReceivingCarrierLandingReady before incoming source)
    (resolved : destinationCurrent before.construction incoming = .ok incoming)
    (different : incoming ≠ source)
    (receiverPresent : before.construction.destinations[incoming]? = some receiver)
    (receiverRole : receiver.use = .receiver)
    (sourcePresent : before.construction.destinations[source]? = some replacement)
    (sourceBuilt : replacement.progress = .built count)
    (adaptation : replacement.adaptation = none)
    (physical : replacement.capability.layout = .varr (.int .u8))
    (logical : replacement.capability.logicalType = .varr (.int .u8)) :
    ∃ after, finishChannels layout [.construct incoming] [.varr (.int .u8)] [.completed source] origin before = .ok () after := by
  obtain ⟨after, landed, _, _, _, frame⟩ :=
    landCarriersInto_construct_completed layout origin before ambient incoming source context backed ready
  obtain ⟨row, present, receiver, adapt, phys, logic, built⟩ :=
    frame.replacement_receiver_metadata before after incoming source count receiver replacement
      resolved different receiverPresent receiverRole sourcePresent sourceBuilt
  have finished := byte_receiver_finishChannel layout origin after source count row present built receiver
    (adapt.trans adaptation) (phys.trans physical) (logic.trans logical)
  refine ⟨after, ?_⟩
  simp only [finishChannels, landed, List.length_cons, List.length_nil, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons,
    List.forIn_nil, bind, pure, finished]

#print axioms land_constructed_byte_finishes
#print axioms CompletedCarrierLandingFrame.replacement_receiver_metadata

end Goose.Proofs.ExitExecution

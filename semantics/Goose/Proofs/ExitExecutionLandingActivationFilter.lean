import Goose.Proofs.ConstructionExitByteFinish
import Goose.Proofs.ExitExecutionLandingMetadata

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem land_constructed_filter_activation (origin : Goose.Core.OriginId)
    (incoming source : Nat) (before after : ExecutionState) (activation : Nat)
    (landed : landCarriersInto origin [.construct incoming] [.completed source] before = .ok () after) :
    landCarriersInto origin [.construct incoming] [.completed source]
      { before with activations := before.activations.filter (fun current => current.act != activation) } =
      .ok () { after with activations := after.activations.filter (fun current => current.act != activation) } := by
  simp only [landCarriersInto, List.length_cons, List.length_nil, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons, List.forIn_nil,
    receivingDestination, liftConstruction, bind, pure] at landed ⊢
  cases resolved : destinationCurrent before.construction incoming with
  | error fault => simp only [resolved, Goose.Construct.fault, EvalM.stop] at landed; cases landed
  | ok receiver =>
    simp only [resolved] at landed ⊢
    by_cases equal : receiver = source
    · simp only [equal, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, ExecutionStep.ok.injEq] at landed ⊢
      rcases landed with ⟨_, rfl⟩
      exact ⟨True.intro, rfl⟩
    · have distinct : (receiver != source) = true := by simp [equal]
      simp only [distinct, ↓reduceIte] at landed ⊢
      cases result : landExitReplacementInto receiver source before.construction with
      | fault reason final => simp only [result] at landed; cases landed
      | ok value final =>
        cases value
        simp only [result, bind, pure, ExecutionStep.ok.injEq] at landed ⊢
        rcases landed with ⟨_, rfl⟩
        exact ⟨True.intro, rfl⟩

theorem land_constructed_byte_finishes_filtered (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (incoming source count activation : Nat)
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
    ∃ after, finishChannels layout [.construct incoming] [.varr (.int .u8)] [.completed source] origin
      { before with activations := before.activations.filter (fun current => current.act != activation) } = .ok () after := by
  obtain ⟨after, landed, _, _, _, frame⟩ :=
    landCarriersInto_construct_completed layout origin before ambient incoming source context backed ready
  obtain ⟨row, present, receiver, adapt, phys, logic, built⟩ :=
    frame.replacement_receiver_metadata before after incoming source count receiver replacement
      resolved different receiverPresent receiverRole sourcePresent sourceBuilt
  have replay := land_constructed_filter_activation origin incoming source before after activation landed
  have finished := byte_receiver_finishChannel layout origin
    { after with activations := after.activations.filter (fun current => current.act != activation) }
    source count row present built receiver (adapt.trans adaptation) (phys.trans physical) (logic.trans logical)
  refine ⟨{ after with activations := after.activations.filter (fun current => current.act != activation) }, ?_⟩
  simp only [finishChannels, replay, List.length_cons, List.length_nil, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons,
    List.forIn_nil, bind, pure, finished]

#print axioms land_constructed_byte_finishes_filtered
#print axioms land_constructed_filter_activation

end Goose.Proofs.ExitExecution

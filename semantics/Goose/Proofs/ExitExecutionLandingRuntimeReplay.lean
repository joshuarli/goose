import Goose.Proofs.ExitExecutionLandingActivationFilter

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem land_constructed_replay (origin : Goose.Core.OriginId)
    (incoming source : Nat) (before after alternate : ExecutionState)
    (same : alternate.construction = before.construction)
    (landed : landCarriersInto origin [.construct incoming] [.completed source] before = .ok () after) :
    landCarriersInto origin [.construct incoming] [.completed source] alternate =
      .ok () { alternate with construction := after.construction } := by
  simp only [landCarriersInto, List.length_cons, List.length_nil, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons, List.forIn_nil,
    receivingDestination, liftConstruction, bind, pure, same] at landed ⊢
  cases resolved : destinationCurrent before.construction incoming with
  | error fault => simp only [resolved, Goose.Construct.fault, EvalM.stop] at landed; cases landed
  | ok receiver =>
    simp only [resolved] at landed ⊢
    by_cases equal : receiver = source
    · simp only [equal, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, ExecutionStep.ok.injEq] at landed ⊢
      rcases landed with ⟨_, rfl⟩
      exact ⟨True.intro, by simp only [same]⟩
    · have distinct : (receiver != source) = true := by simp [equal]
      simp only [distinct, ↓reduceIte] at landed ⊢
      cases result : landExitReplacementInto receiver source before.construction with
      | fault reason final => simp only [result] at landed; cases landed
      | ok value final =>
        cases value
        simp only [result, bind, pure, ExecutionStep.ok.injEq] at landed ⊢
        rcases landed with ⟨_, rfl⟩
        exact ⟨True.intro, rfl⟩

theorem land_constructed_byte_finishes_replay (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (before alternate : ExecutionState) (ambient : OwnershipAmbient) (incoming source count : Nat)
    (receiver replacement : PendingDestination) (same : alternate.construction = before.construction)
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
    ∃ after, finishChannels layout [.construct incoming] [.varr (.int .u8)] [.completed source] origin alternate = .ok () after := by
  obtain ⟨after, landed, _, _, _, frame⟩ :=
    landCarriersInto_construct_completed layout origin before ambient incoming source context backed ready
  obtain ⟨row, present, receiver, adapt, phys, logic, built⟩ :=
    frame.replacement_receiver_metadata before after incoming source count receiver replacement
      resolved different receiverPresent receiverRole sourcePresent sourceBuilt
  have replay := land_constructed_replay origin incoming source before after alternate same landed
  have finished := byte_receiver_finishChannel layout origin { alternate with construction := after.construction }
    source count row present built receiver (adapt.trans adaptation) (phys.trans physical) (logic.trans logical)
  refine ⟨{ alternate with construction := after.construction }, ?_⟩
  simp only [finishChannels, replay, List.length_cons, List.length_nil, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons,
    List.forIn_nil, bind, pure, finished]

#print axioms land_constructed_replay
#print axioms land_constructed_byte_finishes_replay

end Goose.Proofs.ExitExecution

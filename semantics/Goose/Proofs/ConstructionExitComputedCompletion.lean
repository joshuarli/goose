import Goose.Proofs.ConstructionExitWaitingWorld
import Goose.Proofs.ConstructionExitEvaluationHistoryMixedCompletion

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

theorem numeric_prefix_completion_execution (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (source : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (bytes : List UInt8) (origin : OriginId) (operands : List (CheckedNumericOperand source))
    (world : AcceptedWorld config source.initialized before ambient types live regions pending)
    (frame : AcceptedFrame config accepted source before types) (history : EvaluationHistoryCoverage before ambient pending)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (receiver : ready.destination.use = .receiver) (packed : ready.destination.layout = .packed)
    (adaptation : ready.destination.adaptation = none) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32) :
    let token := before.construction.exitReservations.size
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting id) } }
    let channels := operands.map (fun operand => Channel.register operand.ty)
    let expressions := operands.map CheckedNumericOperand.expression
    ∃ after,
      EvaluationHistoryLifecycleOutcome .carriers (channels ++ [.completion token])
        (.completionChannels [token] [] [] :: ambient) pending
        (evalOperands (fuel + operands.length + 5) config source.interpretation.environment
          (channels ++ [.completion token]) (expressions ++ [.bytes (.varr (.int .u8)) bytes origin]) waited) ∧
      ∀ carriers,
      evalOperands (fuel + operands.length + 5) config source.interpretation.environment channels expressions waited =
        .ok carriers waited →
      evalOperands (fuel + operands.length + 5) config source.interpretation.environment
        (channels ++ [.completion token]) (expressions ++ [.bytes (.varr (.int .u8)) bytes origin]) waited =
        .ok (carriers ++ [.completed id]) after ∧
      CarrierResultBacking config.layout after (.completed id) ∧
      CarrierLandingReady after (.completion token) (.completed id) := by
  let token := before.construction.exitReservations.size
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting id) } }
  have waitedWorld := (waitExitDestination_acceptedWorld config source.initialized before ambient types live regions pending id world history.1).2
  have waitedFrame := (acceptedFrame_waitExitDestination id frame).2
  have waitHistory := wait_completion_references_bounded before.construction ambient id [] [] history.1
  have coverage : EvaluationHistoryCoverage waited (.completionChannels [token] [] [] :: ambient) pending := by
    refine ⟨waitHistory.2, ?_⟩
    intro old member
    simp only [OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers, List.nil_append] at member
    exact history.2 old member
  obtain ⟨after, _, byteProduce, _, byteReady, byteBacking, _⟩ :=
    completion_byte_receiver_history (fuel + 2) config source.initialized source.interpretation.environment before ambient
      types live regions pending id bytes origin world history ready receiver packed adaptation request current fits
  change evalProduce (fuel + 4) config source.interpretation.environment [.completion token]
    (.bytes (.varr (.int .u8)) bytes origin) waited = .ok [.completed id] after at byteProduce
  have execution : ∀ (items : List (CheckedNumericOperand source)) (carriers : List Carrier),
      evalOperands (fuel + items.length + 5) config source.interpretation.environment
        (items.map (fun operand => Channel.register operand.ty)) (items.map CheckedNumericOperand.expression) waited =
        .ok carriers waited →
      evalOperands (fuel + items.length + 5) config source.interpretation.environment
        (items.map (fun operand => Channel.register operand.ty) ++ [.completion token])
        (items.map CheckedNumericOperand.expression ++ [.bytes (.varr (.int .u8)) bytes origin]) waited =
        .ok (carriers ++ [.completed id]) after := by
    intro items
    induction items with
    | nil =>
      intro carriers prefixResult
      simp only [List.map_nil, List.length_nil, Nat.add_zero, evalOperands, pure, ExecutionStep.ok.injEq] at prefixResult
      obtain ⟨rfl, _⟩ := prefixResult
      simp only [List.map_nil, List.nil_append, List.length_nil, Nat.add_zero, evalOperands, byteProduce, singleCarrier, bind, pure]
    | cons first rest ih =>
      intro carriers prefixResult
      have head := accepted_numeric_register_outcomes first.form (fuel + rest.length + 4) config accepted source waited
        (.completionChannels [token] [] [] :: ambient) types live regions pending waitedWorld waitedFrame coverage
        first.ty first.roots first.typingAfter first.rootsAfter first.checked
      let action := evalProduce (fuel + rest.length + 5) config source.interpretation.environment [.register first.ty] first.expression
      have tailFuel : fuel + (rest.length + 1) + 5 = (fuel + rest.length + 5) + 1 := by omega
      cases result : action waited with
      | stop reason final | escape target carried final | jump target kind final =>
        dsimp only [action] at result
        simp only [List.map_cons, List.length_cons, tailFuel, evalOperands, result, bind] at prefixResult
        cases prefixResult
      | ok headCarriers final =>
        dsimp only [action] at result
        obtain ⟨value, headEq, finalEq, _, _, _, _⟩ := head.2.2.2.2 headCarriers final result
        subst headCarriers
        subst final
        simp only [List.map_cons, List.length_cons, tailFuel, evalOperands, result, singleCarrier, bind, pure] at prefixResult
        cases tail : evalOperands (fuel + rest.length + 5) config source.interpretation.environment
            (rest.map (fun operand => Channel.register operand.ty)) (rest.map CheckedNumericOperand.expression) waited with
        | stop reason final | escape target carried final | jump target kind final =>
          simp only [tail, bind] at prefixResult
          cases prefixResult
        | ok restCarriers final =>
          simp only [tail, bind, pure, ExecutionStep.ok.injEq] at prefixResult
          obtain ⟨rfl, rfl⟩ := prefixResult
          have mixed := ih restCarriers tail
          simp only [List.map_cons, List.cons_append, List.length_cons, tailFuel, evalOperands,
            result, singleCarrier, bind, pure, mixed, List.cons_append]
  have allOutcomes := completion_mixed_operands_all_outcomes (fuel + operands.length + 5) config source.initialized
    source.interpretation.environment before ambient types live regions pending id
    (operands.map (fun operand => Channel.register operand.ty) ++ [.completion token])
    (operands.map CheckedNumericOperand.expression ++ [.bytes (.varr (.int .u8)) bytes origin]) world history
  refine ⟨after, allOutcomes.2, ?_⟩
  intro carriers prefixResult
  exact ⟨execution operands carriers prefixResult, byteBacking _ (by simp), byteReady.pairs _ _ (by simp [token])⟩

#print axioms numeric_prefix_completion_execution

end Goose.Proofs.ConstructionAcceptedExecution

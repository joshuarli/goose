import Goose.Proofs.ConstructionExitEvaluationHistoryMixed
import Goose.Proofs.ConstructionExitEvaluationHistoryCompletion
import Goose.Proofs.ConstructionExitEvaluationHistoryOutcome
import Goose.Proofs.ConstructionExecutionProtocolReservationReserve

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId IntTy)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem mixed_literal_completion_byte_operands (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (literals : List RegisterLiteral) (id : Nat) (bytes : List UInt8) (origin : OriginId)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (history : EvaluationHistoryCoverage state ambient pending)
    (ready : OpenDestinationBacking config.layout state id (.varr (.int .u8)) 0)
    (receiver : ready.destination.use = .receiver) (packed : ready.destination.layout = .packed)
    (adaptation : ready.destination.adaptation = none) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent state.construction id = .ok id) (fits : bytes.length < 2 ^ 32) :
    let token := state.construction.exitReservations.size
    let waited := { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.push (.waiting id) } }
    let channels := literals.map RegisterLiteral.channel ++ [.completion token]
    let expressions := literals.map RegisterLiteral.expression ++ [.bytes (.varr (.int .u8)) bytes origin]
    let carriers := literals.map RegisterLiteral.carrier ++ [.completed id]
    let frame : PendingCarrierFrame := ⟨channels, carriers⟩
    ∃ after,
      evalOperands (fuel + literals.length + 5) config environment channels expressions waited = .ok carriers after ∧
      EvaluationHistoryCoverage after (.returned carriers :: .completionChannels [token] [] [] :: ambient) (frame :: pending) ∧
      CarriersLandingReady after channels carriers ∧
      (∀ carrier ∈ carriers, CarrierResultBacking config.layout after carrier) ∧
      landCarriersInto origin channels carriers after = .ok () after := by
  let token := state.construction.exitReservations.size
  let waited := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.push (.waiting id) } }
  obtain ⟨after, waitedExecution, byteProduce, returnedHistory, byteReady, byteBacking, byteLanding⟩ :=
    completion_byte_receiver_history (fuel + 2) config initialized environment state ambient types live regions pending id bytes origin
      world history ready receiver packed adaptation request current fits
  change evalProduce (fuel + 4) config environment [.completion token] (.bytes (.varr (.int .u8)) bytes origin) waited = .ok [.completed id] after at byteProduce
  have waitingHistory := wait_completion_references_bounded state.construction ambient id [] [] history.1
  have priorWaited : EvaluationHistoryCoverage waited (.completionChannels [token] [] [] :: ambient) pending := by
    refine ⟨waitingHistory.2, ?_⟩
    intro old member
    simp only [OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers, List.nil_append] at member
    exact history.2 old member
  have prior : EvaluationHistoryCoverage after (.completionChannels [token] [] [] :: ambient) pending := by
    constructor
    · exact (evaluationHistoryCoverage_pop after _ _ _ returnedHistory).1
    · intro old member
      simp only [OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers, List.nil_append] at member
      exact history.2 old member
  have execute : ∀ items : List RegisterLiteral,
      evalOperands (fuel + items.length + 5) config environment
        (items.map RegisterLiteral.channel ++ [.completion token])
        (items.map RegisterLiteral.expression ++ [.bytes (.varr (.int .u8)) bytes origin]) waited =
        .ok (items.map RegisterLiteral.carrier ++ [.completed id]) after := by
    intro items
    induction items with
    | nil =>
      simp only [List.map_nil, List.nil_append, List.length_nil, Nat.add_zero, evalOperands, byteProduce, singleCarrier, bind, pure]
    | cons first rest ih =>
      have head := registerLiteral_produce (fuel + rest.length + 3) config environment waited (.completionChannels [token] [] [] :: ambient) pending first priorWaited
      have step : evalOperands ((fuel + rest.length + 5) + 1) config environment
          (first.channel :: (rest.map RegisterLiteral.channel ++ [.completion token]))
          (first.expression :: (rest.map RegisterLiteral.expression ++ [.bytes (.varr (.int .u8)) bytes origin])) waited =
          .ok (first.carrier :: (rest.map RegisterLiteral.carrier ++ [.completed id])) after := by
        simp only [evalOperands, head, singleCarrier, bind, pure, ih]
      simpa only [List.map_cons, List.cons_append, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step
  have channelsReady : ∀ items : List RegisterLiteral,
      CarriersLandingReady after (items.map RegisterLiteral.channel ++ [.completion token])
        (items.map RegisterLiteral.carrier ++ [.completed id]) := by
    intro items
    induction items with
    | nil =>
      refine ⟨rfl, ?_⟩
      intro channel carrier member
      simp only [List.map_nil, List.nil_append, List.zip_cons_cons, List.zip_nil_left, List.mem_singleton, Prod.mk.injEq] at member
      obtain ⟨rfl, rfl⟩ := member
      exact byteReady.pairs _ _ (by simp [token])
    | cons first rest ih =>
      refine ⟨by simp, ?_⟩
      intro channel carrier member
      simp only [List.map_cons, List.cons_append, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at member
      rcases member with same | tail
      · obtain ⟨rfl, rfl⟩ := same
        cases first <;> exact .register _ _
      · exact ih.pairs channel carrier tail
  have landing : ∀ items : List RegisterLiteral,
      landCarriersInto origin (items.map RegisterLiteral.channel ++ [.completion token])
        (items.map RegisterLiteral.carrier ++ [.completed id]) after = .ok () after := by
    intro items
    induction items with
    | nil => simpa only [List.map_nil, List.nil_append] using byteLanding
    | cons first rest ih =>
      cases first <;>
        simp only [RegisterLiteral.channel, RegisterLiteral.carrier, landCarriersInto, List.map_cons, List.cons_append,
          List.length_cons, List.length_append, List.length_map, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          List.zip_cons_cons, List.forIn_cons, bind, pure] at ih ⊢ <;> exact ih
  refine ⟨after, execute literals, evaluationHistoryCoverage_returned after (.completionChannels [token] [] [] :: ambient) pending _ _ prior,
    channelsReady literals, ?_, landing literals⟩
  intro carrier member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with items | same
  · obtain ⟨literal, found, equal⟩ := List.mem_map.mp items
    subst carrier
    cases literal with
    | integer ty value => exact .register _ (.integer ty value)
    | boolean value => exact .register _ (.boolean value)
  · subst carrier
    exact byteBacking _ (by simp)


theorem completion_mixed_operands_all_outcomes (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (channels : List Channel) (expressions : List Expr)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (history : EvaluationHistoryCoverage before ambient pending) :
    let token := before.construction.exitReservations.size
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting id) } }
    waitExitDestination id before.construction = .ok token waited.construction ∧
    EvaluationHistoryLifecycleOutcome .carriers channels (.completionChannels [token] [] [] :: ambient) pending
      (evalOperands fuel config environment channels expressions waited) := by
  let token := before.construction.exitReservations.size
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting id) } }
  have waitHistory := wait_completion_references_bounded before.construction ambient id [] [] history.1
  have lifecycle := Goose.Proofs.ConstructionExecutionProtocol.waitExitDestination_reservation_lifecycle id
    before.construction world.ownership.source.structural.1.1
  have waitedLifecycle : ReservationLifecycleInvariant waited.construction := by
    simpa only [waitHistory.1, ConstructionResult.finalState] using lifecycle
  have coverage : EvaluationHistoryCoverage waited (.completionChannels [token] [] [] :: ambient) pending := by
    refine ⟨waitHistory.2, ?_⟩
    intro item member
    simp only [OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers, List.nil_append] at member
    exact history.2 item member
  exact ⟨waitHistory.1, evaluator_history_outcome fuel config .carriers _
    (.operands environment channels expressions) waited _ pending channels ⟨waitedLifecycle, coverage⟩⟩

#print axioms completion_mixed_operands_all_outcomes

#print axioms mixed_literal_completion_byte_operands

end Goose.Proofs.ConstructionAcceptedExecution

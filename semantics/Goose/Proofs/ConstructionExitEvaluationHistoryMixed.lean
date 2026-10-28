import Goose.Proofs.ConstructionExitEvaluationHistoryProduced
import Goose.Proofs.ConstructionExitEvaluationHistoryRegister
import Goose.Proofs.ConstructionExitDirectByteLoop
import Goose.Proofs.ConstructionExitByteProduce

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId IntTy)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

inductive RegisterLiteral where
  | integer (ty : IntTy) (value : Int)
  | boolean (value : Bool)

def RegisterLiteral.channel : RegisterLiteral → Channel
  | .integer ty _ => .register (.int ty)
  | .boolean _ => .register .bool

def RegisterLiteral.expression : RegisterLiteral → Expr
  | .integer ty value => .lit ty value
  | .boolean value => .bool value

def RegisterLiteral.carrier : RegisterLiteral → Carrier
  | .integer ty value => .register (.int ty value)
  | .boolean value => .register (.bool value)

theorem registerLiteral_produce (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (state : ExecutionState) (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame)
    (literal : RegisterLiteral) (history : EvaluationHistoryCoverage state ambient pending) :
    evalProduce (fuel + 2) config environment [literal.channel] literal.expression state = .ok [literal.carrier] state := by
  cases literal with
  | integer ty value => exact (integer_register_history_returned fuel config environment state ambient pending ty value history).1
  | boolean value => exact (boolean_register_history_returned fuel config environment state ambient pending value history).1

theorem mixed_literal_byte_operands (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (literals : List RegisterLiteral) (id : Nat) (bytes : List UInt8) (origin : OriginId)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (history : EvaluationHistoryCoverage state ambient pending)
    (ready : OpenDestinationBacking config.layout state id (.varr (.int .u8)) 0)
    (receiver : ready.destination.use = .receiver) (packed : ready.destination.layout = .packed)
    (adaptation : ready.destination.adaptation = none) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent state.construction id = .ok id) (fits : bytes.length < 2 ^ 32) :
    let channels := literals.map RegisterLiteral.channel ++ [.construct id]
    let expressions := literals.map RegisterLiteral.expression ++ [.bytes (.varr (.int .u8)) bytes origin]
    let carriers := literals.map RegisterLiteral.carrier ++ [.completed id]
    let frame : PendingCarrierFrame := ⟨channels, carriers⟩
    ∃ after,
      evalOperands (fuel + literals.length + 5) config environment channels expressions state = .ok carriers after ∧
      EvaluationHistoryCoverage after (.returned carriers :: ambient) (frame :: pending) ∧
      CarriersLandingReady after channels carriers ∧
      (∀ carrier ∈ carriers, CarrierResultBacking config.layout after carrier) ∧
      landCarriersInto origin channels carriers after = .ok () after := by
  obtain ⟨after, built⟩ := packed_receiver_byte_build (fuel + 2) config environment bytes origin state id 0
    ready.destination ready.storage ready.present ready.bytes ready.opened packed adaptation receiver request current (by simpa using fits)
  have produced := accepted_byte_construct_produce_unwind (fuel + 2) config initialized environment bytes origin id 0 state after
    ambient types live regions pending world ready packed request receiver (by simpa using fits) current built 0 0
  have byteProduce : evalProduce (fuel + 4) config environment [.construct id] (.bytes (.varr (.int .u8)) bytes origin) state =
      .ok [.completed id] after := by simpa only [Nat.add_assoc] using produced.1
  have backed := accepted_byte_receiver_landing_ready (fuel + 2) config initialized environment bytes origin id 0
    state after ambient types live regions pending world ready packed request receiver (by simpa using fits) current built
  obtain ⟨byteBacking, ⟨byteReady⟩, byteLanding⟩ := backed
  have tickets := buildExpr_bytes_tickets (fuel + 2) config environment id (.varr (.int .u8)) bytes origin
    state after ready.destination 0 world.ownership.source current ready.present ready.opened built
  have prior : EvaluationHistoryCoverage after ambient pending := by
    constructor
    · apply reservationReferencesBounded_mono state.construction after.construction ambient _ history.1
      rw [tickets]
      exact Nat.le_refl _
    · exact history.2
  have execute : ∀ items : List RegisterLiteral,
      evalOperands (fuel + items.length + 5) config environment
        (items.map RegisterLiteral.channel ++ [.construct id])
        (items.map RegisterLiteral.expression ++ [.bytes (.varr (.int .u8)) bytes origin]) state =
        .ok (items.map RegisterLiteral.carrier ++ [.completed id]) after := by
    intro items
    induction items with
    | nil =>
      simp only [List.map_nil, List.nil_append, List.length_nil, Nat.add_zero, evalOperands, byteProduce, singleCarrier, bind, pure]
    | cons first rest ih =>
      have head := registerLiteral_produce (fuel + rest.length + 3) config environment state ambient pending first history
      have step : evalOperands ((fuel + rest.length + 5) + 1) config environment
          (first.channel :: (rest.map RegisterLiteral.channel ++ [.construct id]))
          (first.expression :: (rest.map RegisterLiteral.expression ++ [.bytes (.varr (.int .u8)) bytes origin])) state =
          .ok (first.carrier :: (rest.map RegisterLiteral.carrier ++ [.completed id])) after := by
        simp only [evalOperands, head, singleCarrier, bind, pure, ih]
      simpa only [List.map_cons, List.cons_append, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step
  have channelsReady : ∀ items : List RegisterLiteral,
      CarriersLandingReady after (items.map RegisterLiteral.channel ++ [.construct id])
        (items.map RegisterLiteral.carrier ++ [.completed id]) := by
    intro items
    induction items with
    | nil =>
      refine ⟨rfl, ?_⟩
      intro channel carrier member
      simp only [List.map_nil, List.nil_append, List.zip_cons_cons, List.zip_nil_left, List.mem_singleton, Prod.mk.injEq] at member
      obtain ⟨rfl, rfl⟩ := member
      exact .construct id id byteReady
    | cons first rest ih =>
      refine ⟨by simp, ?_⟩
      intro channel carrier member
      simp only [List.map_cons, List.cons_append, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at member
      rcases member with same | tail
      · obtain ⟨rfl, rfl⟩ := same
        cases first <;> exact .register _ _
      · exact ih.pairs channel carrier tail
  have landing : ∀ items : List RegisterLiteral,
      landCarriersInto origin (items.map RegisterLiteral.channel ++ [.construct id])
        (items.map RegisterLiteral.carrier ++ [.completed id]) after = .ok () after := by
    intro items
    induction items with
    | nil => simpa only [List.map_nil, List.nil_append] using byteLanding
    | cons first rest ih =>
      cases first <;>
        simp only [RegisterLiteral.channel, RegisterLiteral.carrier, landCarriersInto, List.map_cons, List.cons_append,
          List.length_cons, List.length_append, List.length_map, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          List.zip_cons_cons, List.forIn_cons, bind, pure] at ih ⊢ <;> exact ih
  refine ⟨after, execute literals, evaluationHistoryCoverage_returned after ambient pending _ _ prior,
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
    exact byteBacking

#print axioms mixed_literal_byte_operands

end Goose.Proofs.ConstructionAcceptedExecution

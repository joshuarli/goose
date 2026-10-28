import Goose.Proofs.ConstructionExitEvaluationHistoryRead
import Goose.Proofs.ConstructionExitEvaluationHistoryRegister

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId IntTy)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

structure RegisterOperand where
  ty : Ty
  expression : Expr
  value : Value

inductive RegisterOperandSource (environment : RuntimeActivation) (state : ExecutionState)
    (live : RootInst → Prop) : RegisterOperand → Prop
  | integer (ty : IntTy) (value : Int) :
      RegisterOperandSource environment state live ⟨.int ty, .lit ty value, .int ty value⟩
  | boolean (value : Bool) :
      RegisterOperandSource environment state live ⟨.bool, .bool value, .bool value⟩
  | global (global : Nat) (ty : Ty) (value : Value)
      (rootLive : live (.global global)) (present : state.objects.lookup (.global global) = some value) :
      RegisterOperandSource environment state live ⟨ty, .read (.global global), value⟩
  | localRoot (localVar scopeInst : Nat) (descriptor : LocalVar) (ty : Ty) (value : Value)
      (descriptorFound : environment.vars[localVar]? = some descriptor)
      (scopeFound : environment.scopes.find? (fun entry => entry.1 == descriptor.scope) = some (descriptor.scope, scopeInst))
      (rootLive : live (.local environment.act scopeInst localVar))
      (present : state.objects.lookup (.local environment.act scopeInst localVar) = some value) :
      RegisterOperandSource environment state live ⟨ty, .read (.var localVar), value⟩

theorem accepted_register_operand (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (operand : RegisterOperand) (world : AcceptedWorld config initialized state ambient types live regions pending)
    (history : EvaluationHistoryCoverage state ambient pending) (source : RegisterOperandSource environment state live operand) :
    evalProduce (fuel + 3) config environment [.register operand.ty] operand.expression state = .ok [.register operand.value] state ∧
      CarrierResultBacking config.layout state (.register operand.value) := by
  cases source with
  | integer ty value =>
    have result := integer_register_history_returned (fuel + 1) config environment state ambient pending ty value history
    exact ⟨by simpa only [Nat.add_assoc] using result.1, result.2.2.2.1 _ (by simp)⟩
  | boolean value =>
    have result := boolean_register_history_returned (fuel + 1) config environment state ambient pending value history
    exact ⟨by simpa only [Nat.add_assoc] using result.1, result.2.2.2.1 _ (by simp)⟩
  | global global ty value rootLive present =>
    have result := accepted_global_read_register_history fuel config initialized environment state ambient types live regions pending
      global ty value 0 world history rootLive present
    exact ⟨result.1, result.2.2.2.1 _ (by simp)⟩
  | localRoot localVar scopeInst descriptor ty value descriptorFound scopeFound rootLive present =>
    have result := accepted_local_read_register_history fuel config initialized environment state ambient types live regions pending
      localVar scopeInst descriptor ty value 0 world history descriptorFound scopeFound rootLive present
    exact ⟨result.1, result.2.2.2.1 _ (by simp)⟩

theorem accepted_register_operands (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (operands : List RegisterOperand) (world : AcceptedWorld config initialized state ambient types live regions pending)
    (history : EvaluationHistoryCoverage state ambient pending)
    (sources : ∀ operand ∈ operands, RegisterOperandSource environment state live operand) :
    let channels := operands.map (fun operand => Channel.register operand.ty)
    let carriers := operands.map (fun operand => Carrier.register operand.value)
    let expressions := operands.map RegisterOperand.expression
    let frame : PendingCarrierFrame := ⟨channels, carriers⟩
    evalOperands (fuel + operands.length + 3) config environment channels expressions state = .ok carriers state ∧
      EvaluationHistoryCoverage state (.returned carriers :: ambient) (frame :: pending) ∧
      CarriersLandingReady state channels carriers ∧
      (∀ carrier ∈ carriers, CarrierResultBacking config.layout state carrier) ∧
      landCarriersInto 0 channels carriers state = .ok () state := by
  have execution : ∀ (items : List RegisterOperand),
      (∀ operand ∈ items, RegisterOperandSource environment state live operand) →
      evalOperands (fuel + items.length + 3) config environment
        (items.map (fun operand => .register operand.ty)) (items.map RegisterOperand.expression) state =
        .ok (items.map (fun operand => .register operand.value)) state := by
    intro items
    induction items with
    | nil => intro valid; simp [evalOperands, pure]
    | cons first rest ih =>
      intro valid
      have head := accepted_register_operand (fuel + rest.length) config initialized environment state ambient types live regions pending
        first world history (valid first (by simp))
      have tail := ih (fun operand member => valid operand (List.mem_cons_of_mem first member))
      have step : evalOperands ((fuel + rest.length + 3) + 1) config environment
          (.register first.ty :: rest.map (fun operand => .register operand.ty))
          (first.expression :: rest.map RegisterOperand.expression) state =
          .ok (.register first.value :: rest.map (fun operand => .register operand.value)) state := by
        simp only [evalOperands, head.1, singleCarrier, bind, pure, tail]
      simpa only [List.map_cons, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step
  have ready : ∀ items : List RegisterOperand,
      CarriersLandingReady state (items.map (fun operand => .register operand.ty))
        (items.map (fun operand => .register operand.value)) := by
    intro items
    induction items with
    | nil => exact ⟨rfl, by simp⟩
    | cons first rest ih =>
      refine ⟨by simp, ?_⟩
      intro channel carrier member
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at member
      rcases member with same | tail
      · obtain ⟨rfl, rfl⟩ := same
        exact .register _ _
      · exact ih.pairs channel carrier tail
  have landing : ∀ items : List RegisterOperand,
      landCarriersInto 0 (items.map (fun operand => .register operand.ty))
        (items.map (fun operand => .register operand.value)) state = .ok () state := by
    intro items
    induction items with
    | nil => simp [landCarriersInto, bind, pure]
    | cons first rest ih =>
      simp only [landCarriersInto, List.map_cons, List.length_cons, List.length_map, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.forIn_cons, bind, pure] at ih ⊢
      exact ih
  refine ⟨execution operands sources, evaluationHistoryCoverage_returned state ambient pending _ _ history,
    ready operands, ?_, landing operands⟩
  intro carrier member
  obtain ⟨operand, found, equal⟩ := List.mem_map.mp member
  subst carrier
  exact (accepted_register_operand 0 config initialized environment state ambient types live regions pending operand
    world history (sources operand found)).2

#print axioms accepted_register_operands
#print axioms accepted_register_operand

end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionExitEvaluationHistoryFrames
import Goose.Proofs.ConstructionExitProducedFrame

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem integer_register_history_returned (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (state : ExecutionState) (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame)
    (ty : Goose.Core.IntTy) (value : Int) (history : EvaluationHistoryCoverage state ambient pending) :
    let frame : PendingCarrierFrame := ⟨[.register (.int ty)], [.register (.int ty value)]⟩
    evalProduce (fuel + 2) config environment frame.channels (.lit ty value) state = .ok frame.carriers state ∧
      EvaluationHistoryCoverage state (.returned frame.carriers :: ambient) (frame :: pending) ∧
      CarriersLandingReady state frame.channels frame.carriers ∧
      (∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout state carrier) ∧
      landCarriersInto 0 frame.channels frame.carriers state = .ok () state := by
  refine ⟨?_, evaluationHistoryCoverage_returned state ambient pending [.register (.int ty)] [.register (.int ty value)] history, ?_, ?_, ?_⟩
  · simp only [evalProduce, List.mapM_cons, List.mapM_nil, selectCompletionChannel, evalValue, bind, pure]
  · refine ⟨rfl, ?_⟩
    intro channel carrier member
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    exact .register _ _
  · intro carrier member
    simp only [List.mem_singleton] at member
    subst carrier
    exact .register _ (.integer ty value)
  · simp only [landCarriersInto, List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons, List.forIn_nil, bind, pure]

theorem boolean_register_history_returned (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (state : ExecutionState) (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame)
    (value : Bool) (history : EvaluationHistoryCoverage state ambient pending) :
    let frame : PendingCarrierFrame := ⟨[.register .bool], [.register (.bool value)]⟩
    evalProduce (fuel + 2) config environment frame.channels (.bool value) state = .ok frame.carriers state ∧
      EvaluationHistoryCoverage state (.returned frame.carriers :: ambient) (frame :: pending) ∧
      CarriersLandingReady state frame.channels frame.carriers ∧
      (∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout state carrier) ∧
      landCarriersInto 0 frame.channels frame.carriers state = .ok () state := by
  refine ⟨?_, evaluationHistoryCoverage_returned state ambient pending [.register .bool] [.register (.bool value)] history, ?_, ?_, ?_⟩
  · simp only [evalProduce, List.mapM_cons, List.mapM_nil, selectCompletionChannel, evalValue, bind, pure]
  · refine ⟨rfl, ?_⟩
    intro channel carrier member
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    exact .register _ _
  · intro carrier member
    simp only [List.mem_singleton] at member
    subst carrier
    exact .register _ (.boolean value)
  · simp only [landCarriersInto, List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons, List.forIn_nil, bind, pure]

#print axioms integer_register_history_returned
#print axioms boolean_register_history_returned

end Goose.Proofs.ConstructionAcceptedExecution

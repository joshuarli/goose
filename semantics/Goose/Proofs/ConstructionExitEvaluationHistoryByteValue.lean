import Goose.Proofs.ConstructionExitEvaluationHistoryOutcome
import Goose.Proofs.ConstructionByteValueComplete
import Goose.Proofs.ExitExecutionLiveCarriers

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

theorem accepted_byte_value_register_outcomes (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (bytes : List UInt8) (origin : OriginId)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (history : EvaluationHistoryCoverage state ambient pending) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame (.bytes (.varr (.int .u8)) bytes origin) ty roots typingAfter rootsAfter) :
    let action := evalProduce (fuel + 1) config frame.interpretation.environment [.register ty]
      (.bytes (.varr (.int .u8)) bytes origin)
    let outcome := action state
    EvaluationHistoryLifecycleOutcome .carriers [.register ty] ambient pending outcome ∧
      (∃ nextRegions, AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live nextRegions pending ∧
        AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types) ∧
      (∀ carriers after, outcome = .ok carriers after →
        ∃ value, carriers = [.register value] ∧
          AcceptedValue config.layout types frame.interpretation after ty roots value ∧
          CarriersLandingReady after [.register ty] carriers ∧
          (∀ carrier ∈ carriers, CarrierResultBacking config.layout after carrier) ∧
          landCarriersInto origin [.register ty] carriers after = .ok () after) := by
  let expression : Expr := .bytes (.varr (.int .u8)) bytes origin
  have equation : evalProduce (fuel + 1) config frame.interpretation.environment [.register ty] expression state =
      (do let value ← evalValue fuel config frame.interpretation.environment expression; pure [Goose.Construct.Carrier.register value]) state := by
    simp only [expression, evalProduce, List.mapM_cons, List.mapM_nil, selectCompletionChannel, bind, pure]
  have stepSame : Goose.Proofs.Exit.stepState
      (evalProduce (fuel + 1) config frame.interpretation.environment [.register ty] expression state) =
      Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment expression state) := by
    rw [equation]
    cases evaluated : evalValue fuel config frame.interpretation.environment expression state <;>
      simp only [bind, evaluated, pure, Goose.Proofs.Exit.stepState]
  have historyValid : EvaluationHistoryLifecycle state ambient pending := ⟨world.ownership.source.structural.1.1, history⟩
  have historyOutcome := evaluator_history_outcome (fuel + 1) config .carriers _
    (.produce frame.interpretation.environment [.register ty] expression) state ambient pending [.register ty] historyValid
  obtain ⟨nextRegions, finalWorld, finalSource, valueAccepted⟩ :=
    evalValue_checkedByteOwner_complete fuel config accepted frame state bytes origin ambient types live regions pending
      ty roots typingAfter rootsAfter world source checked
  have sameByteStep : Goose.Proofs.Exit.stepState
      (evalProduce (fuel + 1) config frame.interpretation.environment [.register ty] (.bytes (.varr (.int .u8)) bytes origin) state) =
      Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment (.bytes (.varr (.int .u8)) bytes origin) state) := stepSame
  refine ⟨historyOutcome, ?_, ?_⟩
  · refine ⟨nextRegions, ?_, ?_⟩
    · rw [sameByteStep]; exact finalWorld
    · rw [sameByteStep]; exact finalSource
  · intro carriers after success
    change evalProduce (fuel + 1) config frame.interpretation.environment [.register ty] expression state = .ok carriers after at success
    rw [equation] at success
    cases evaluated : evalValue fuel config frame.interpretation.environment expression state with
    | stop reason final | escape target carried final | jump target kind final =>
      simp only [bind, evaluated] at success
      cases success
    | ok value final =>
      simp only [bind, evaluated, pure, ExecutionStep.ok.injEq] at success
      obtain ⟨rfl, rfl⟩ := success
      change evalValue fuel config frame.interpretation.environment (.bytes (.varr (.int .u8)) bytes origin) state = .ok value final at evaluated
      simp only [evaluated, Goose.Proofs.Exit.stepState] at valueAccepted
      have acceptedValue := valueAccepted value rfl
      refine ⟨value, rfl, acceptedValue, ?_, ?_, ?_⟩
      · refine ⟨rfl, ?_⟩
        intro channel carrier member
        simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton, Prod.mk.injEq] at member
        obtain ⟨rfl, rfl⟩ := member
        exact .register _ _
      · intro carrier member
        simp only [List.mem_singleton] at member
        subst carrier
        exact .register _ acceptedValue.backed
      · simp only [landCarriersInto, List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true,
          ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons, List.forIn_nil, bind, pure]

#print axioms accepted_byte_value_register_outcomes

end Goose.Proofs.ConstructionAcceptedExecution

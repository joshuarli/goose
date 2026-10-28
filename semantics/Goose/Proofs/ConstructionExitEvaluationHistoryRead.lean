import Goose.Proofs.ConstructionExitEvaluationHistoryOutcome
import Goose.Proofs.ConstructionExitProducedFrame

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst GlobalId OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem accepted_global_read_register_history (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (global : GlobalId) (ty : Ty) (value : Value) (origin : OriginId)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (history : EvaluationHistoryCoverage state ambient pending)
    (rootLive : live (.global global)) (present : state.objects.lookup (.global global) = some value) :
    let frame : PendingCarrierFrame := ⟨[.register ty], [.register value]⟩
    evalProduce (fuel + 3) config environment frame.channels (.read (.global global)) state = .ok frame.carriers state ∧
      EvaluationHistoryCoverage state (.returned frame.carriers :: ambient) (frame :: pending) ∧
      CarriersLandingReady state frame.channels frame.carriers ∧
      (∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout state carrier) ∧
      landCarriersInto origin frame.channels frame.carriers state = .ok () state := by
  refine ⟨?_, evaluationHistoryCoverage_returned state ambient pending [.register ty] [.register value] history, ?_, ?_, ?_⟩
  · simp only [evalProduce, List.mapM_cons, List.mapM_nil, selectCompletionChannel, evalValue, evalPlace,
      readLoc, EvalM.get, present, readValuePath, bind, pure]
  · refine ⟨rfl, ?_⟩
    intro channel carrier member
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    exact .register _ _
  · intro carrier member
    simp only [List.mem_singleton] at member
    subst carrier
    exact .register _ (world.backing.values (.global global) rootLive value present)
  · simp only [landCarriersInto, List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons, List.forIn_nil, bind, pure]

theorem accepted_local_read_register_history (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (localVar scopeInst : Nat) (descriptor : LocalVar) (ty : Ty) (value : Value) (origin : OriginId)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (history : EvaluationHistoryCoverage state ambient pending)
    (descriptorFound : environment.vars[localVar]? = some descriptor)
    (scopeFound : environment.scopes.find? (fun entry => entry.1 == descriptor.scope) = some (descriptor.scope, scopeInst))
    (rootLive : live (.local environment.act scopeInst localVar))
    (present : state.objects.lookup (.local environment.act scopeInst localVar) = some value) :
    let frame : PendingCarrierFrame := ⟨[.register ty], [.register value]⟩
    evalProduce (fuel + 3) config environment frame.channels (.read (.var localVar)) state = .ok frame.carriers state ∧
      EvaluationHistoryCoverage state (.returned frame.carriers :: ambient) (frame :: pending) ∧
      CarriersLandingReady state frame.channels frame.carriers ∧
      (∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout state carrier) ∧
      landCarriersInto origin frame.channels frame.carriers state = .ok () state := by
  refine ⟨?_, evaluationHistoryCoverage_returned state ambient pending [.register ty] [.register value] history, ?_, ?_, ?_⟩
  · simp only [evalProduce, List.mapM_cons, List.mapM_nil, selectCompletionChannel, evalValue, evalPlace,
      rootOf, descriptorFound, scopeFound, readLoc, EvalM.get, present, readValuePath, bind, pure]
  · refine ⟨rfl, ?_⟩
    intro channel carrier member
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    exact .register _ _
  · intro carrier member
    simp only [List.mem_singleton] at member
    subst carrier
    exact .register _ (world.backing.values (.local environment.act scopeInst localVar) rootLive value present)
  · simp only [landCarriersInto, List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons, List.forIn_nil, bind, pure]

#print axioms accepted_local_read_register_history
#print axioms accepted_global_read_register_history

end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionGhostSyntaxFuel
import Goose.Proofs.ConstructionGhostBuilderCallEvents

namespace Goose.Proofs.ConstructionGhostBuilderChannelWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostBuilderCallEvents
open Goose.Proofs.ConstructionExecution

private def bytes : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def context : Context := ⟨0, "target", [], [], []⟩
private def implementation : Impl := ⟨"target", #[], #[⟨.varr (.int .u8), .value, none⟩], #[], .mk 1 [] (some bytes), .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state
private def ready : ExecutionState := stepState (newDestination config.layout 0 (.varr (.int .u8)) .value 0 none (some 2) .initial)

private theorem argumentsSyntax : ∀ id actualImplementation start finish,
    getImplementation config 0 start = .ok (id, actualImplementation) finish →
    ArgumentSyntax config actualImplementation.params.toList [] := by
  intro id actualImplementation start finish lookup
  obtain ⟨actualContext, found, idEq, implemented⟩ := implementation_lookup_source config 0 start finish id actualImplementation lookup
  have contextEq : actualContext = context := by simpa [config] using found.symm
  subst actualContext
  subst id
  have implEq : actualImplementation = implementation := by simpa [config, context] using implemented.symm
  subst actualImplementation
  exact .nil

private theorem closed : ClosedModuleWithTails config := by
  intro contextId actualContext actualImplementation found implemented
  cases contextId with
  | zero =>
      have contextEq : actualContext = context := by simpa [config] using found.symm
      subst actualContext
      have implEq : actualImplementation = implementation := by simpa [config, context] using implemented.symm
      subst actualImplementation
      exact ⟨1, [], some bytes, rfl, (by simp), .constructed bytes (.bytes _ _ _) (.bytes _ _ _) (.bytes _ _ _)⟩
  | succ n => simp [config] at found

theorem builderCall_events : ∃ after,
    SourceHistory config 40 [] (.builder environment 0 (.call 0 [] 0)) ready
      (buildExpr 40 config environment 0 (.call 0 [] 0) ready) ∧
    buildExpr 40 config environment 0 (.call 0 [] 0) ready = .ok () after ∧
    after.construction.events = [.begin 0, .write 0 0, .write 0 1] := by
  have support := (syntaxFuel_existsWithTails 40 config closed).builder environment 0 (.call 0 [] 0)
    (.channelCall 0 [] 0 argumentsSyntax)
  have history := fuelHistory_exists 40 config _ [] ready support
  refine ⟨stepState (buildExpr 40 config environment 0 (.call 0 [] 0) ready), history, ?_, ?_⟩
  · simp only [stepState, ready, config, context, implementation, environment, bytes]
    cbv
  · simp only [stepState, ready, config, context, implementation, environment, bytes]
    cbv

private def callReady : ExecutionState := stepState (liftConstruction 0 (renewReceivingDestination 0) ready)

theorem builderCall_childEvents :
    SourceHistory config 39 [0] (.channelCall environment 0 [] [.construct 0] 0) callReady
      (invokeCall 39 config environment 0 [] [.construct 0] 0 callReady) ∧
    EventPrefix (Goose.Proofs.Exit.stepState (invokeCall 39 config environment 0 [] [.construct 0] 0 callReady)).construction.events
      (Goose.Proofs.Exit.stepState (buildExpr 40 config environment 0 (.call 0 [] 0) ready)).construction.events ∧
    (Goose.Proofs.Exit.stepState (buildExpr 40 config environment 0 (.call 0 [] 0) ready)).construction.events =
      [.begin 0, .write 0 0, .write 0 1] := by
  obtain ⟨after, history, execution, events⟩ := builderCall_events
  have renewed : liftConstruction 0 (renewReceivingDestination 0) ready = .ok 0 callReady := by
    simp only [callReady, ready, stepState, config, context, implementation, environment, bytes]
    cbv
  refine ⟨builderCall_child_history history 39 environment 0 0 0 [] 0 callReady rfl rfl renewed,
    builderCall_sourcePrefix 39 config environment 0 0 0 [] 0 ready callReady renewed, ?_⟩
  rw [execution]
  exact events

#print axioms builderCall_childEvents
#print axioms builderCall_events
end Goose.Proofs.ConstructionGhostBuilderChannelWitness

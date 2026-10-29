import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostBuilderResultWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel

private def bytes : Expr := .bytes (.varr (.int .u8)) [65] 0
private def resultBlock : Block := .mk 1 [] (some bytes)
private def blockSource : Expr := .blockE resultBlock 0
private def singleSource : Expr := .values [bytes]
private def conditionalSource : Expr := .ifE (.bool true) resultBlock resultBlock 0
private def global (source : Expr) : Global := ⟨"global", .varr (.int .u8), .immutable, source, 0⟩
private def context : Context := ⟨0, "entry", [], [], []⟩
private def implementation : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩
private def config (source : Expr) : EvalConfig := ⟨.release,
  ⟨#[], #[], #[global source], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem closed (source : Expr) : ClosedModule (config source) := by
  intro id ctx impl found implemented
  cases id with
  | zero =>
      have ctxEq : ctx = context := by simpa [config] using found.symm
      subst ctx
      have implEq : impl = implementation := by simpa [config, context] using implemented.symm
      subst impl
      exact ⟨0, [], rfl, by simp⟩
  | succ n => simp [config] at found

private theorem resultSyntax (source : Expr) : ResultBlockSyntax (config source) resultBlock := by
  exact .make 1 [] (some bytes) (by simp) (.produced bytes (.bytes _ _ _) (.bytes _ _ _) (.bytes _ _ _))

theorem block_history (fuel : Nat) (environment : RuntimeActivation) (destination : Goose.Core.DestinationId) (before : ExecutionState) :
    SourceHistory (config blockSource) fuel [] (.builder environment destination blockSource) before
      (buildExpr fuel (config blockSource) environment destination blockSource before) := by
  apply fuelHistory_exists
  exact (syntaxFuel_exists fuel (config blockSource) (closed blockSource)).builder environment destination blockSource
    (.block resultBlock 0 (resultSyntax blockSource))

theorem conditional_history (fuel : Nat) (environment : RuntimeActivation) (destination : Goose.Core.DestinationId) (before : ExecutionState) :
    SourceHistory (config conditionalSource) fuel [] (.builder environment destination conditionalSource) before
      (buildExpr fuel (config conditionalSource) environment destination conditionalSource before) := by
  apply fuelHistory_exists
  exact (syntaxFuel_exists fuel (config conditionalSource) (closed conditionalSource)).builder environment destination conditionalSource
    (.conditional (.bool true) resultBlock resultBlock 0 (.base (.boolean true)) (resultSyntax conditionalSource) (resultSyntax conditionalSource))

theorem single_history (fuel : Nat) (environment : RuntimeActivation) (destination : Goose.Core.DestinationId) (before : ExecutionState) :
    SourceHistory (config singleSource) fuel [] (.builder environment destination singleSource) before
      (buildExpr fuel (config singleSource) environment destination singleSource before) := by
  apply fuelHistory_exists
  exact (syntaxFuel_exists fuel (config singleSource) (closed singleSource)).builder environment destination singleSource
    (.singleValue bytes (.bytes _ _ _))

theorem conditional_producer_history (fuel : Nat) (environment : RuntimeActivation) (channels : List Channel) (before : ExecutionState) :
    SourceHistory (config conditionalSource) fuel [] (.producerWith environment channels conditionalSource) before
      (evalProduce fuel (config conditionalSource) environment channels conditionalSource before) := by
  apply fuelHistory_exists
  exact (syntaxFuel_exists fuel (config conditionalSource) (closed conditionalSource)).conditionalProducer environment channels
    (.bool true) resultBlock resultBlock 0 (.base (.boolean true)) (resultSyntax conditionalSource) (resultSyntax conditionalSource)

theorem actual_events :
    runModule 40 (config blockSource) .initial = .ok () (stepState (runModule 40 (config blockSource) .initial)) ∧
    runModule 40 (config conditionalSource) .initial = .ok () (stepState (runModule 40 (config conditionalSource) .initial)) ∧
    (stepState (runModule 40 (config blockSource) .initial)).construction.events = [.begin 0, .write 0 0, .publish 0] ∧
    (stepState (runModule 40 (config conditionalSource) .initial)).construction.events = [.begin 0, .write 0 0, .publish 0] := by
  simp only [stepState, config, global, context, implementation, blockSource, conditionalSource, resultBlock, bytes]
  repeat' constructor <;> cbv

#print axioms block_history
#print axioms conditional_history
#print axioms single_history
#print axioms conditional_producer_history
#print axioms actual_events
end Goose.Proofs.ConstructionGhostBuilderResultWitness

import Goose.Proofs.ConstructionGhostProducerSyntax
import Goose.Proofs.ConstructionGhostResultLocalProducer

namespace Goose.Proofs.ConstructionGhostResultLocalWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostProducerSyntax

private def context : Context := ⟨0, "entry", [], [], []⟩
private def implementation : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def descriptor : LocalVar := ⟨"value", .bool, .immutable, 0, 0⟩
private def environment : RuntimeActivation := ⟨0, 0, #[descriptor], [(0, 0)], []⟩
private def action : EvalM (List Carrier) := do
  bindRoot (.local 0 0 0) (.bool true)
  evalProduce 40 config environment [.register .bool] (.resultLocal 0 0)
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem closed : ClosedModuleWithTails config := by
  intro id actualContext actualImplementation found implemented
  cases id with
  | zero =>
      have contextEq : actualContext = context := by simpa [config] using found.symm
      subst actualContext
      have implEq : actualImplementation = implementation := by simpa [config, context] using implemented.symm
      subst actualImplementation
      exact ⟨0, [], none, rfl, by simp, .none⟩
  | succ n => simp [config] at found

theorem resultLocal_history (fuel : Nat) (before : ExecutionState) :
    SourceHistory config fuel [] (.producerWith environment [.register .bool] (.resultLocal 0 0)) before
      (evalProduce fuel config environment [.register .bool] (.resultLocal 0 0) before) :=
  producerSyntax_history fuel config closed environment [.register .bool] (.resultLocal 0 0) before (.resultLocal 0 0)

theorem resultLocal_actual : action .initial = .ok [.register (.bool true)] (stepState (action .initial)) := by
  simp only [stepState, action, config, context, implementation, environment, descriptor]
  cbv

#print axioms resultLocal_history
#print axioms resultLocal_actual
end Goose.Proofs.ConstructionGhostResultLocalWitness

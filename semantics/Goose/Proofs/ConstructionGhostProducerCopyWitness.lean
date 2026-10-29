import Goose.Proofs.ConstructionGhostProducerCopy

namespace Goose.Proofs.ConstructionGhostProducerCopyWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostProducerCopy

private def global : Global := ⟨"global", .bool, .immutable, .bool true, 0⟩
private def context : Context := ⟨0, "entry", [], [], []⟩
private def implementation : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[global], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def action : EvalM (List Carrier) := do
  initGlobals 40 config [0]
  evalProduce 40 config environment [.register .bool] (.copy .bool (.global 0) 0)
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

theorem copy_history (fuel : Nat) (before : ExecutionState) :
    SourceHistory config fuel [] (.producerWith environment [.register .bool] (.copy .bool (.global 0) 0)) before
      (evalProduce fuel config environment [.register .bool] (.copy .bool (.global 0) 0) before) :=
  copyProducer_history fuel config closed environment [.register .bool] .bool (.global 0) 0 before (.globalPlace 0)

theorem copy_actual : action .initial = .ok [.register (.bool true)] (stepState (action .initial)) := by
  simp only [stepState, action, config, context, implementation, global, environment]
  cbv

#print axioms copy_history
#print axioms copy_actual
end Goose.Proofs.ConstructionGhostProducerCopyWitness

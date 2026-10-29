import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostValueListsWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel

private def context : Context := ⟨0, "entry", [], [], []⟩
private def implementation : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def nested : Expr := .push (.global 0) (.lit .u8 1) (some 0)

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

theorem singleton_history (fuel : Nat) (before : ExecutionState) :
    SourceHistory config fuel [] (.value environment (.values [.bool true])) before
      (evalValue fuel config environment (.values [.bool true]) before) :=
  fuelHistory_exists fuel config _ [] before ((syntaxFuel_existsWithTails fuel config closed).value environment _
    (.singletonValue (.bool true) (.base (.boolean true))))

theorem arity_precedes_operands :
    evalValue 20 config environment (.values [nested, .bool true]) .initial = .stop (.fault .arity) .initial := by
  simp [evalValue, fault, EvalM.stop]

#print axioms singleton_history
#print axioms arity_precedes_operands
end Goose.Proofs.ConstructionGhostValueListsWitness

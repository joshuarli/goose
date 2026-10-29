import Goose.Proofs.ConstructionGhostProducerOperands
import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostProducerOperandsWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostProducerOperands

private def context : Context := ⟨0, "entry", [], [], []⟩
private def implementation : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def operands : List Expr := [.bool true, .bool false]
private def channels : List Channel := [.register .bool, .register .bool]

private theorem closed : ClosedModule config := by
  intro id actualContext actualImplementation found implemented
  cases id with
  | zero =>
      have contextEq : actualContext = context := by simpa [config] using found.symm
      subst actualContext
      have implEq : actualImplementation = implementation := by simpa [config, context] using implemented.symm
      subst actualImplementation
      exact ⟨0, [], rfl, by simp⟩
  | succ n => simp [config] at found

private theorem supported (fuel : Nat) (channel : Channel) (operand : Expr) (member : operand ∈ operands) :
    FuelSupport config fuel (.producerWith environment [channel] operand) := by
  simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact (syntaxFuel_exists fuel config closed).supportedProducer environment [channel] (.bool true) (.boolean true)
  · exact (syntaxFuel_exists fuel config closed).supportedProducer environment [channel] (.bool false) (.boolean false)

theorem values_history (fuel : Nat) :
    SourceHistory config fuel [] (.producerWith environment channels (.values operands)) .initial
      (evalProduce fuel config environment channels (.values operands) .initial) := by
  apply fuelHistory_exists
  exact valuesFuel fuel config environment channels operands (by
    intro childFuel channel operand lower member
    exact supported childFuel channel operand member)

theorem values_actual :
    evalProduce 20 config environment channels (.values operands) .initial =
      .ok [.register (.bool true), .register (.bool false)] .initial := by
  simp only [config, context, implementation, environment, channels, operands]
  cbv

theorem mismatched_actual :
    evalOperands 20 config environment [] operands .initial = .stop (.fault .arity) .initial ∧
    evalOperands 0 config environment channels operands .initial = .stop .timeout .initial := by
  constructor <;> simp [evalOperands, operands, channels, fault, Goose.Construct.timeout, EvalM.stop]

#print axioms values_history
#print axioms values_actual
#print axioms mismatched_actual
end Goose.Proofs.ConstructionGhostProducerOperandsWitness

import Goose.Proofs.ConstructionGhostProducerSyntax
import Goose.Proofs.ConstructionGhostSourceGlobal

namespace Goose.Proofs.ConstructionGhostValuesEntryWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostProducerSyntax
open Goose.Proofs.ConstructionGhostSourceGlobal

private def operands : List Expr := [.bool true, .bool false]
private def expression : Expr := .values operands
private def channels : List Channel := [.register .bool, .register .bool]
private def context : Context := ⟨0, "entry", [], [], []⟩
private def implementation : Impl := ⟨"entry", #[], #[⟨.bool, .register, none⟩, ⟨.bool, .register, none⟩], #[],
  .mk 0 [] (some expression), .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem children : ∀ operand ∈ operands, ProducerSyntax config operand := by
  intro operand member
  simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .constructed (.bool true) (.supported (.boolean true)) (.base (.boolean true)) (.supported _ (.boolean true))
  · exact .constructed (.bool false) (.supported (.boolean false)) (.base (.boolean false)) (.supported _ (.boolean false))

private theorem closed : ClosedModuleWithTails config := by
  intro id actualContext actualImplementation found implemented
  cases id with
  | zero =>
      have contextEq : actualContext = context := by simpa [config] using found.symm
      subst actualContext
      have implEq : actualImplementation = implementation := by simpa [config, context] using implemented.symm
      subst actualImplementation
      exact ⟨0, [], some expression, rfl, by simp, .producer expression (.values operands children)⟩
  | succ n => simp [config] at found

private theorem argumentsSyntax : ∀ id actual start ready,
    getImplementation config 0 start = .ok (id, actual) ready → ArgumentSyntax config actual.params.toList [] := by
  intro id actual start ready lookup
  obtain ⟨foundContext, found, idEq, implemented⟩ := implementation_lookup_source config 0 start ready id actual lookup
  have contextEq : foundContext = context := by simpa [config] using found.symm
  subst foundContext
  subst id
  have implEq : actual = implementation := by simpa [config, context] using implemented.symm
  subst actual
  exact .nil

theorem entry_history (fuel : Nat) :
    SourceHistory config fuel [] (.channelCall environment 0 [] channels 0) .initial
      (invokeCall fuel config environment 0 [] channels 0 .initial) :=
  fuelHistory_exists fuel config _ [] .initial
    ((syntaxFuel_existsWithTails fuel config closed).channelCall environment 0 [] channels 0 argumentsSyntax)

theorem entry_actual :
    runModule 40 config .initial = entryCallResult (invokeCall 40 config environment 0 [] channels 0 .initial) ∧
    runModule 40 config .initial = .ok () (stepState (runModule 40 config .initial)) := by
  simp only [stepState, config, context, implementation, environment, channels, expression, operands]
  constructor <;> cbv

#print axioms entry_history
#print axioms entry_actual
end Goose.Proofs.ConstructionGhostValuesEntryWitness

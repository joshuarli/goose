import Goose.Proofs.ConstructionGhostProducerSyntax

namespace Goose.Proofs.ConstructionGhostValuesTailWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostProducerSyntax

private def context : Context := ⟨0, "entry", [], [], []⟩
private def implementation : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def operands : List Expr := [.bool true, .bool false]
private def channels : List Channel := [.register .bool, .register .bool]
private def block : Block := .mk 1 [] (some (.values operands))
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

private theorem children : ∀ operand ∈ operands, ProducerSyntax config operand := by
  intro operand member
  simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .constructed (.bool true) (.supported (.boolean true)) (.base (.boolean true)) (.supported _ (.boolean true))
  · exact .constructed (.bool false) (.supported (.boolean false)) (.base (.boolean false)) (.supported _ (.boolean false))

private theorem blockSyntax : ResultBlockSyntax config block :=
  .make 1 [] (some (.values operands)) (by simp) (.values operands children)

theorem valuesTail_history (fuel : Nat) (before : ExecutionState) :
    SourceHistory config fuel [] (.resultBlock environment channels block) before
      (execResultBlock fuel config environment channels block before) :=
  fuelHistory_exists fuel config _ [] before ((syntaxFuel_existsWithTails fuel config closed).resultBlock environment channels block blockSyntax)

theorem valuesTail_actual :
    execResultBlock 40 config environment channels block .initial =
      .ok (.normal .unit, [.register (.bool true), .register (.bool false)])
        (stepState (execResultBlock 40 config environment channels block .initial)) := by
  simp only [stepState, config, context, implementation, environment, channels, block, operands]
  cbv

#print axioms valuesTail_history
#print axioms valuesTail_actual
end Goose.Proofs.ConstructionGhostValuesTailWitness

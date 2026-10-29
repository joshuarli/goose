import Goose.Proofs.ConstructionGhostSyntaxFuel
import Goose.Proofs.ConstructionGhostPushCore

namespace Goose.Proofs.ConstructionGhostPushNonfixedWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostScalarProducer

private def ty : Ty := .grow (.varr (.int .u8))
private def operand : Expr := .bytes (.varr (.int .u8)) [66] 0
private def expression : Expr := .push (.global 0) operand (some 0)
private def global : Global := ⟨"global", ty, .mutable, .arrLit ty [] 0, 0⟩
private def context : Context := ⟨0, "entry", [], [], []⟩
private def implementation : Impl := ⟨"entry", #[], #[], #[], .mk 0 [.expr expression 0] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[global], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def action : EvalM (Nat × Bool) := do
  runModule 40 config
  arrayLength (← readLoc 40 config.layout ⟨.global 0, []⟩)
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem source : ValueSyntax config expression :=
  .push (.global 0) operand (some 0) (.globalPlace 0) (.bytes _ _ _) (.bytes _ _ _)

private theorem closed : ClosedModuleWithTails config := by
  intro id actualContext actualImplementation found implemented
  cases id with
  | zero =>
      have contextEq : actualContext = context := by simpa [config] using found.symm
      subst actualContext
      have implEq : actualImplementation = implementation := by simpa [config, context] using implemented.symm
      subst actualImplementation
      refine ⟨0, [.expr expression 0], none, rfl, ?_, .none⟩
      intro statement member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst statement
      exact .expression expression 0 source
  | succ n => simp [config] at found

theorem push_history (fuel : Nat) (before : ExecutionState) :
    SourceHistory config fuel [] (.value environment expression) before (evalValue fuel config environment expression before) :=
  fuelHistory_exists fuel config _ [] before ((syntaxFuel_existsWithTails fuel config closed).value environment expression source)

theorem push_actual : action .initial = .ok (1, true) (stepState (action .initial)) := by
  simp only [stepState, action, config, context, implementation, global, environment, expression, operand, ty]
  cbv

#print axioms push_history
#print axioms push_actual
end Goose.Proofs.ConstructionGhostPushNonfixedWitness

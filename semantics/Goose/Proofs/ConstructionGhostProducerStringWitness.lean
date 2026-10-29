import Goose.Proofs.ConstructionGhostProducerString

namespace Goose.Proofs.ConstructionGhostProducerStringWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostProducerString

private def ty : Ty := .varr (.int .u8)
private def arguments : List PrintArg := [.text "A", .expr (.lit .i64 7)]
private def expression : Expr := .str ty arguments 0
private def global : Global := ⟨"global", ty, .immutable, expression, 0⟩
private def context : Context := ⟨0, "entry", [], [], []⟩
private def implementation : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[global], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
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

private theorem children : ∀ argument ∈ arguments, PrintArgumentSyntax config argument := by
  intro argument member
  simp only [arguments, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .text "A"
  · exact .expression (.lit .i64 7) (.base (.integer .i64 7))

theorem string_history (fuel : Nat) (before : ExecutionState) :
    SourceHistory config fuel [] (.producerWith environment [.register ty] expression) before
      (evalProduce fuel config environment [.register ty] expression before) :=
  stringProducer_history fuel config closed environment [.register ty] ty arguments 0 before children

theorem string_actual :
    runModule 40 config .initial = .ok () (stepState (runModule 40 config .initial)) ∧
    (stepState (runModule 40 config .initial)).construction.events = [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
  simp only [stepState, config, context, implementation, global, expression, arguments, ty]
  constructor <;> cbv

#print axioms string_history
#print axioms string_actual
end Goose.Proofs.ConstructionGhostProducerStringWitness

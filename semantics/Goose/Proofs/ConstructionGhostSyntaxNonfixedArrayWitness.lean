import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostSyntaxNonfixedArrayWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel

private def element : Ty := .varr (.int .u8)
private def first : Expr := .bytes element [65] 0
private def second : Expr := .bytes element [66] 0
private def operands : List Expr := [first, second]
private def expression : Expr := .arrLit (.varr element) operands 0
private def statements : List Stmt := [.letS 0 expression 0, .expr expression 0]
private def context : Context := ⟨0, "entry", [], [], []⟩
private def implementation : Impl := ⟨"entry", #[], #[], #[⟨"nested", .varr element, .immutable, 0, 0⟩],
  .mk 0 statements none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem values : ∀ operand ∈ operands, ValueSyntax config operand := by
  intro operand member
  simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .bytes _ _ _

private theorem builders : ∀ operand ∈ operands, DeclarationBuilderSyntax config operand := by
  intro operand member
  simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .bytes _ _ _

private theorem builder : DeclarationBuilderSyntax config expression := .array (.varr element) operands 0 values builders
private theorem value : ValueSyntax config expression := .nonfixedArray (.varr element) operands 0 rfl builder

private theorem closed : ClosedModule config := by
  intro contextId actualContext actualImplementation contextFound implementationFound
  cases contextId with
  | zero =>
      have contextEq : actualContext = context := by simpa [config] using contextFound.symm
      subst actualContext
      have implementationEq : actualImplementation = implementation := by simpa [config, context] using implementationFound.symm
      subst actualImplementation
      refine ⟨0, statements, rfl, ?_⟩
      intro statement member
      simp only [statements, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .declaration 0 expression 0 value builder
      · exact .expression expression 0 value
  | succ n => simp [config] at contextFound

theorem module_history (fuel : Nat) : ∃ outcome,
    SourceHistory config fuel [] (.callWith ⟨0, 0, #[], [], []⟩ 0 [] 0) .initial outcome ∧
      runModule fuel config .initial = moduleCallResult outcome :=
  syntaxModule_history fuel config closed context implementation rfl rfl rfl rfl rfl

theorem module_arrayPaths : ∃ outcome,
    SourceHistory config 60 [] (.callWith ⟨0, 0, #[], [], []⟩ 0 [] 0) .initial outcome ∧
    runModule 60 config .initial = moduleCallResult outcome ∧
    runModule 60 config .initial = .ok () (stepState (runModule 60 config .initial)) ∧
    (stepState (runModule 60 config .initial)).construction.events ≠ [] := by
  obtain ⟨outcome, history, execution⟩ := module_history 60
  refine ⟨outcome, history, execution, ?_, ?_⟩
  · simp only [stepState, config, context, implementation, statements, expression, operands, first, second, element]
    cbv
  · simp only [stepState, config, context, implementation, statements, expression, operands, first, second, element]
    cbv
    intro impossible
    cases impossible

#print axioms module_history
#print axioms module_arrayPaths
end Goose.Proofs.ConstructionGhostSyntaxNonfixedArrayWitness

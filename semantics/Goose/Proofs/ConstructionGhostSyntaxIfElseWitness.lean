import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostSyntaxIfElseWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel

private def yesBytes : Expr := .bytes (.varr (.int .u8)) [65] 0
private def noBytes : Expr := .bytes (.varr (.int .u8)) [66] 0
private def yesStatements : List Stmt := [.letS 0 yesBytes 0, .print [.text "yes"] 0]
private def noStatements : List Stmt := [.letS 1 noBytes 0, .print [.text "no"] 0]
private def statements : List Stmt := [.ifS (.bool false) (.mk 1 yesStatements none) (some (.mk 2 noStatements none)) 0]
private def context : Context := ⟨0, "entry", [], [], []⟩
private def implementation : Impl := ⟨"entry", #[], #[],
  #[⟨"yes", .varr (.int .u8), .immutable, 1, 0⟩, ⟨"no", .varr (.int .u8), .immutable, 2, 0⟩],
  .mk 0 statements none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem yesSyntax : ∀ statement ∈ yesStatements, StatementSyntax config statement := by
  intro statement member
  simp only [yesStatements, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .declaration 0 yesBytes 0 (.bytes _ _ _) (.bytes _ _ _)
  · exact .printText "yes" 0

private theorem noSyntax : ∀ statement ∈ noStatements, StatementSyntax config statement := by
  intro statement member
  simp only [noStatements, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .declaration 1 noBytes 0 (.bytes _ _ _) (.bytes _ _ _)
  · exact .printText "no" 0

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
      subst statement
      exact .ifElseStatement (.bool false) 1 yesStatements 2 noStatements 0 (.base (.boolean false)) yesSyntax noSyntax
  | succ n => simp [config] at contextFound

theorem module_history (fuel : Nat) : ∃ outcome,
    SourceHistory config fuel [] (.callWith ⟨0, 0, #[], [], []⟩ 0 [] 0) .initial outcome ∧
      runModule fuel config .initial = moduleCallResult outcome :=
  syntaxModule_history fuel config closed context implementation rfl rfl rfl rfl rfl

theorem module_choosesElse : ∃ outcome,
    SourceHistory config 40 [] (.callWith ⟨0, 0, #[], [], []⟩ 0 [] 0) .initial outcome ∧
    runModule 40 config .initial = moduleCallResult outcome ∧
    runModule 40 config .initial = .ok () (stepState (runModule 40 config .initial)) ∧
    (stepState (runModule 40 config .initial)).construction.events = [.begin 0, .write 0 0, .publish 0] ∧
    (stepState (runModule 40 config .initial)).construction.stdout.data.toList = [110, 111, 10] := by
  obtain ⟨outcome, history, execution⟩ := module_history 40
  refine ⟨outcome, history, execution, ?_, ?_, ?_⟩ <;>
    simp only [stepState, config, context, implementation, statements, yesStatements, noStatements, yesBytes, noBytes] <;> cbv

#print axioms module_history
#print axioms module_choosesElse
end Goose.Proofs.ConstructionGhostSyntaxIfElseWitness

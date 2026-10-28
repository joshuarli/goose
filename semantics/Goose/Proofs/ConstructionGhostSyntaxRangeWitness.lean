import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostSyntaxRangeWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel

private def bytes : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def bodyStatements : List Stmt := [.letS 1 bytes 0]
private def statements : List Stmt := [.forRange 0 (.lit .i64 0) (.lit .i64 2) (.mk 1 bodyStatements none) 0]
private def context : Context := ⟨0, "entry", [], [], []⟩
private def implementation : Impl := ⟨"entry", #[], #[],
  #[⟨"index", .int .i64, .immutable, 1, 0⟩, ⟨"bytes", .varr (.int .u8), .immutable, 1, 0⟩],
  .mk 0 statements none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem bodySyntax : ∀ statement ∈ bodyStatements, StatementSyntax config statement := by
  intro statement member
  simp only [bodyStatements, List.mem_cons, List.not_mem_nil, or_false] at member
  subst statement
  exact .declaration 1 bytes 0 (.bytes _ _ _) (.bytes _ _ _)

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
      exact .rangeStatement 0 (.lit .i64 0) (.lit .i64 2) 1 bodyStatements 0
        (.base (.integer .i64 0)) (.base (.integer .i64 2)) bodySyntax
  | succ n => simp [config] at contextFound

theorem module_history (fuel : Nat) : ∃ outcome,
    SourceHistory config fuel [] (.callWith ⟨0, 0, #[], [], []⟩ 0 [] 0) .initial outcome ∧
      runModule fuel config .initial = moduleCallResult outcome :=
  syntaxModule_history fuel config closed context implementation rfl rfl rfl rfl rfl

theorem module_twoIterations : ∃ outcome,
    SourceHistory config 50 [] (.callWith ⟨0, 0, #[], [], []⟩ 0 [] 0) .initial outcome ∧
    runModule 50 config .initial = moduleCallResult outcome ∧
    runModule 50 config .initial = .ok () (stepState (runModule 50 config .initial)) ∧
    (stepState (runModule 50 config .initial)).construction.events =
      [.begin 0, .write 0 0, .write 0 1, .publish 0, .begin 1, .write 1 0, .write 1 1, .publish 1] := by
  obtain ⟨outcome, history, execution⟩ := module_history 50
  refine ⟨outcome, history, execution, ?_, ?_⟩ <;>
    simp only [stepState, config, context, implementation, statements, bodyStatements, bytes] <;> cbv

#print axioms module_history
#print axioms module_twoIterations
end Goose.Proofs.ConstructionGhostSyntaxRangeWitness

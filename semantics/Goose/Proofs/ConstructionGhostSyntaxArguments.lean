import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostSyntaxArguments
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel

private def entryContext : Context := ⟨0, "entry", [], [], []⟩
private def targetContext : Context := ⟨1, "target", [], [], []⟩
private def argument : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def entryStatements : List Stmt := [.expr (.call 1 [.construct argument] 0) 0]
private def targetStatements : List Stmt := [.print [.text "x"] 0]
private def entryImplementation : Impl := ⟨"entry", #[], #[], #[], .mk 0 entryStatements none, .unknown⟩
private def targetImplementation : Impl := ⟨"target", #[⟨0, .byValue⟩], #[],
  #[⟨"value", .varr (.int .u8), .immutable, 0, 0⟩], .mk 1 targetStatements none, .unknown⟩
private def config : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[entryImplementation, targetImplementation], #[entryContext, targetContext], 0, #[], #[], #[]⟩⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem entryStatements_syntax : ∀ statement ∈ entryStatements, StatementSyntax config statement := by
  intro statement member
  simp only [entryStatements, List.mem_cons, List.not_mem_nil, or_false] at member
  subst statement
  apply StatementSyntax.expression
  apply ValueSyntax.call 1 [.construct argument] 0 targetContext targetImplementation
  · rfl
  · rfl
  · rfl
  · change ArgumentSyntax config [⟨0, .byValue⟩] [.construct argument]
    apply ArgumentSyntax.construct
    · exact .bytes (.varr (.int .u8)) [65, 66] 0
    · intro environment destination
      exact .builderBytes environment destination (.varr (.int .u8)) [65, 66] 0
    · exact .nil

private theorem targetStatements_syntax : ∀ statement ∈ targetStatements, StatementSyntax config statement := by
  intro statement member
  simp only [targetStatements, List.mem_cons, List.not_mem_nil, or_false] at member
  subst statement
  exact .printText "x" 0

private theorem closed : ClosedModule config := by
  intro contextId context implementation contextFound implementationFound
  cases contextId with
  | zero =>
      have contextEq : context = entryContext := by simpa [config] using contextFound.symm
      subst context
      have implementationEq : implementation = entryImplementation := by simpa [config, entryContext] using implementationFound.symm
      subst implementation
      exact ⟨0, entryStatements, rfl, entryStatements_syntax⟩
  | succ contextId =>
      cases contextId with
      | zero =>
          have contextEq : context = targetContext := by simpa [config] using contextFound.symm
          subst context
          have implementationEq : implementation = targetImplementation := by simpa [config, targetContext] using implementationFound.symm
          subst implementation
          exact ⟨1, targetStatements, rfl, targetStatements_syntax⟩
      | succ contextId => simp [config] at contextFound

theorem constructedModule_history (fuel : Nat) : ∃ outcome,
    SourceHistory config fuel [] (.callWith ⟨0, 0, #[], [], []⟩ 0 [] 0) .initial outcome ∧
      runModule fuel config .initial = moduleCallResult outcome :=
  syntaxModule_history fuel config closed entryContext entryImplementation rfl rfl rfl rfl rfl

theorem constructedModule_witness : ∃ state,
    runModule 40 config .initial = .ok () state ∧ state.construction.stdout.data.toList = [120, 10] ∧
    state.construction.events = [.begin 0, .write 0 0, .write 0 1, .publish 0] ∧
    ∃ outcome, SourceHistory config 40 [] (.callWith ⟨0, 0, #[], [], []⟩ 0 [] 0) .initial outcome ∧
      runModule 40 config .initial = moduleCallResult outcome := by
  obtain ⟨outcome, history, execution⟩ := constructedModule_history 40
  refine ⟨stepState (runModule 40 config .initial), ?_, ?_, ?_, outcome, history, execution⟩ <;>
    unfold stepState config entryContext targetContext entryImplementation targetImplementation entryStatements targetStatements argument <;> cbv

#print axioms constructedModule_history
#print axioms constructedModule_witness
end Goose.Proofs.ConstructionGhostSyntaxArguments

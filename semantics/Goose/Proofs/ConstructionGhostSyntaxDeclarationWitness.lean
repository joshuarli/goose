import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostSyntaxDeclarationWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel

private def entry : Context := ⟨0, "entry", [], [], []⟩
private def callee : Context := ⟨1, "callee", [], [], []⟩
private def expression : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def entryBody : List Stmt := [.expr (.call 1 [] 0) 0]
private def calleeBody : List Stmt := [.letS 0 expression 0]
private def entryImpl : Impl := ⟨"entry", #[], #[], #[], .mk 0 entryBody none, .unknown⟩
private def calleeImpl : Impl := ⟨"callee", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 1, 0⟩],
  .mk 1 calleeBody none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[entryImpl, calleeImpl], #[entry, callee], 0, #[], #[], #[]⟩⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem closed : ClosedModule config := by
  intro contextId context implementation contextFound implementationFound
  cases contextId with
  | zero =>
      have same : context = entry := by simpa [config] using contextFound.symm
      subst context
      have same : implementation = entryImpl := by simpa [config, entry] using implementationFound.symm
      subst implementation
      refine ⟨0, entryBody, rfl, ?_⟩
      intro statement member
      simp only [entryBody, List.mem_cons, List.not_mem_nil, or_false] at member
      subst statement
      exact .expression _ 0 (.call 1 [] 0 callee calleeImpl rfl rfl rfl .nil)
  | succ contextId =>
      cases contextId with
      | zero =>
          have same : context = callee := by simpa [config] using contextFound.symm
          subst context
          have same : implementation = calleeImpl := by simpa [config, callee] using implementationFound.symm
          subst implementation
          refine ⟨1, calleeBody, rfl, ?_⟩
          intro statement member
          simp only [calleeBody, List.mem_cons, List.not_mem_nil, or_false] at member
          subst statement
          exact .declaration 0 expression 0 (.bytes _ _ _) (.bytes _ _ _)
      | succ contextId => simp [config] at contextFound

theorem module_history (fuel : Nat) : ∃ outcome,
    SourceHistory config fuel [] (.callWith ⟨0, 0, #[], [], []⟩ 0 [] 0) .initial outcome ∧
      runModule fuel config .initial = moduleCallResult outcome :=
  syntaxModule_history fuel config closed entry entryImpl rfl rfl rfl rfl rfl

theorem module_nonempty : ∃ state,
    runModule 40 config .initial = .ok () state ∧ state.construction.events ≠ [] ∧
    ∃ outcome, SourceHistory config 40 [] (.callWith ⟨0, 0, #[], [], []⟩ 0 [] 0) .initial outcome ∧
      runModule 40 config .initial = moduleCallResult outcome := by
  obtain ⟨outcome, history, execution⟩ := module_history 40
  refine ⟨stepState (runModule 40 config .initial), ?_, ?_, outcome, history, execution⟩
  · unfold stepState config entry callee entryImpl calleeImpl entryBody calleeBody expression
    cbv
  · unfold stepState config entry callee entryImpl calleeImpl entryBody calleeBody expression
    cbv
    intro impossible
    cases impossible

#print axioms module_history
#print axioms module_nonempty
end Goose.Proofs.ConstructionGhostSyntaxDeclarationWitness

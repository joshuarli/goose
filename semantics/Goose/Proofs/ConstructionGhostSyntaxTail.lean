import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostSyntaxTail
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel

private def entryContext : Context := ⟨0, "entry", [], [], []⟩
private def targetContext : Context := ⟨1, "target", [], [], []⟩
private def entryImplementation : Impl := ⟨"entry", #[], #[⟨.unit, .register, none⟩], #[],
  .mk 0 [.print [.text "x"] 0] (some (.call 1 [] 0)), .unknown⟩
private def targetImplementation : Impl := ⟨"target", #[], #[⟨.unit, .register, none⟩], #[],
  .mk 1 [.print [.text "y"] 0] none, .unknown⟩
private def config : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[entryImplementation, targetImplementation], #[entryContext, targetContext], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem argumentsSyntax (contextId : Goose.Core.ContextId) : ∀ id implementation start ready,
    getImplementation config contextId start = .ok (id, implementation) ready →
    ArgumentSyntax config implementation.params.toList [] := by
  intro id implementation start ready lookup
  obtain ⟨context, found, idEqual, implFound⟩ := implementation_lookup_source config contextId start ready id implementation lookup
  subst id
  cases contextId with
  | zero =>
      have contextEq : context = entryContext := by simpa [config] using found.symm
      subst context
      have implEq : implementation = entryImplementation := by simpa [config, entryContext] using implFound.symm
      subst implementation
      exact .nil
  | succ n =>
      cases n with
      | zero =>
          have contextEq : context = targetContext := by simpa [config] using found.symm
          subst context
          have implEq : implementation = targetImplementation := by simpa [config, targetContext] using implFound.symm
          subst implementation
          exact .nil
      | succ n => simp [config] at found

private theorem closed : ClosedModuleWithTails config := by
  intro contextId context implementation found implFound
  cases contextId with
  | zero =>
      have contextEq : context = entryContext := by simpa [config] using found.symm
      subst context
      have implEq : implementation = entryImplementation := by simpa [config, entryContext] using implFound.symm
      subst implementation
      refine ⟨0, [.print [.text "x"] 0], some (.call 1 [] 0), rfl, ?_, .call 1 [] 0 (argumentsSyntax 1)⟩
      intro statement member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst statement
      exact .printText "x" 0
  | succ n =>
      cases n with
      | zero =>
          have contextEq : context = targetContext := by simpa [config] using found.symm
          subst context
          have implEq : implementation = targetImplementation := by simpa [config, targetContext] using implFound.symm
          subst implementation
          refine ⟨1, [.print [.text "y"] 0], none, rfl, ?_, .none⟩
          intro statement member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          subst statement
          exact .printText "y" 0
      | succ n => simp [config] at found

theorem callTail_history (fuel : Nat) :
    SourceHistory config fuel [] (.value environment (.call 0 [] 0)) .initial
      (evalValue fuel config environment (.call 0 [] 0) .initial) := by
  exact fuelHistory_exists fuel config _ [] .initial
    ((syntaxFuel_existsWithTails fuel config closed).value environment (.call 0 [] 0)
      (.channelCall 0 [] 0 (argumentsSyntax 0)))

theorem callTail_success : ∃ after,
    evalValue 60 config environment (.call 0 [] 0) .initial = .ok .unit after ∧
    after.construction.stdout.data.toList = [120, 10, 121, 10] ∧
    SourceHistory config 60 [] (.value environment (.call 0 [] 0)) .initial (.ok .unit after) := by
  have history := callTail_history 60
  refine ⟨stepState (evalValue 60 config environment (.call 0 [] 0) .initial), ?_, ?_, ?_⟩
  · unfold stepState config entryContext targetContext entryImplementation targetImplementation environment
    cbv
  · unfold stepState config entryContext targetContext entryImplementation targetImplementation environment
    cbv
  · have actual : evalValue 60 config environment (.call 0 [] 0) .initial =
        .ok .unit (stepState (evalValue 60 config environment (.call 0 [] 0) .initial)) := by
      unfold stepState config entryContext targetContext entryImplementation targetImplementation environment
      cbv
    rw [actual] at history
    exact history

#print axioms callTail_history
#print axioms callTail_success
end Goose.Proofs.ConstructionGhostSyntaxTail

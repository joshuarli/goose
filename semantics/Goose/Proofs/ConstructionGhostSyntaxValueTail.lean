import Goose.Proofs.ConstructionGhostSyntaxTail

namespace Goose.Proofs.ConstructionGhostSyntaxValueTail
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel

private def context : Context := ⟨0, "value", [], [], []⟩
private def implementation : Impl := ⟨"value", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [.print [.text "x"] 0] (some (.lit .i64 7)), .unknown⟩
private def config : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem argumentsSyntax : ∀ id implementation start ready,
    getImplementation config 0 start = .ok (id, implementation) ready → ArgumentSyntax config implementation.params.toList [] := by
  intro id actualImplementation start ready lookup
  obtain ⟨actualContext, found, idEqual, implFound⟩ := implementation_lookup_source config 0 start ready id actualImplementation lookup
  have contextEq : actualContext = context := by simpa [config] using found.symm
  subst actualContext
  subst id
  have implEq : actualImplementation = implementation := by simpa [config, context] using implFound.symm
  subst actualImplementation
  exact .nil

private theorem closed : ClosedModuleWithTails config := by
  intro contextId actualContext actualImplementation found implFound
  cases contextId with
  | zero =>
      have contextEq : actualContext = context := by simpa [config] using found.symm
      subst actualContext
      have implEq : actualImplementation = implementation := by simpa [config, context] using implFound.symm
      subst actualImplementation
      refine ⟨0, [.print [.text "x"] 0], some (.lit .i64 7), rfl, ?_, .value _ (.integer .i64 7)⟩
      intro statement member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst statement
      exact .printText "x" 0
  | succ n => simp [config] at found

theorem valueTail_history (fuel : Nat) :
    SourceHistory config fuel [] (.value environment (.call 0 [] 0)) .initial
      (evalValue fuel config environment (.call 0 [] 0) .initial) := by
  exact fuelHistory_exists fuel config _ [] .initial
    ((syntaxFuel_existsWithTails fuel config closed).value environment (.call 0 [] 0)
      (.channelCall 0 [] 0 argumentsSyntax))

theorem valueTail_success : ∃ after,
    evalValue 40 config environment (.call 0 [] 0) .initial = .ok (.int .i64 7) after ∧
    after.construction.stdout.data.toList = [120, 10] ∧
    SourceHistory config 40 [] (.value environment (.call 0 [] 0)) .initial (.ok (.int .i64 7) after) := by
  have history := valueTail_history 40
  refine ⟨stepState (evalValue 40 config environment (.call 0 [] 0) .initial), ?_, ?_, ?_⟩
  · unfold stepState config context implementation environment
    cbv
  · unfold stepState config context implementation environment
    cbv
  · have actual : evalValue 40 config environment (.call 0 [] 0) .initial =
        .ok (.int .i64 7) (stepState (evalValue 40 config environment (.call 0 [] 0) .initial)) := by
      unfold stepState config context implementation environment
      cbv
    rw [actual] at history
    exact history

#print axioms valueTail_history
#print axioms valueTail_success
end Goose.Proofs.ConstructionGhostSyntaxValueTail

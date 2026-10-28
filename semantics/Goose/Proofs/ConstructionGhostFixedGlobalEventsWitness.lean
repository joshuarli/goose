import Goose.Proofs.ConstructionGhostFixedGlobalEvents

namespace Goose.Proofs.ConstructionGhostFixedGlobalEventsWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSyntaxFuel
open Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostFixedGlobalEvents
open Goose.Proofs.ConstructionInvocationReplay

private def context : Context := ⟨0, "entry", [], [], []⟩
private def implementation : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩
private def expression : Expr := .len (.val (.bytes (.varr (.int .u8)) [65, 66] 0))
private def global : Global := ⟨"length", .int .i64, .immutable, expression, 0⟩
private def config : EvalConfig := ⟨.release,
  ⟨#[], #[], #[global], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem closed : ClosedModuleWithTails config := by
  intro contextId actualContext actualImplementation found implFound
  cases contextId with
  | zero =>
      have contextEq : actualContext = context := by simpa [config] using found.symm
      subst actualContext
      have implEq : actualImplementation = implementation := by simpa [config, context] using implFound.symm
      subst actualImplementation
      exact ⟨0, [], none, rfl, by simp, .none⟩
  | succ n => simp [config] at found

private theorem expressionSyntax : ValueSyntax config expression :=
  .length (.val (.bytes (.varr (.int .u8)) [65, 66] 0))
    (.value _ (.bytes (.varr (.int .u8)) [65, 66] 0))

theorem fixedGlobal_sourceEvents : ∃ after visits,
    OperandReplay (globalInitializer 40 config) 0 [0] [] .initial (.ok [()] after) visits ∧
    (∃ visit ∈ visits,
      let environment : RuntimeActivation := ⟨0, visit.before.nextAct, #[], [], []⟩
      let ready := { visit.before with nextAct := visit.before.nextAct + 1 }
      SourceHistory config 40 [visit.ordinal, 0] (.value environment expression) ready
        (evalValue 40 config environment expression ready) ∧
      (Goose.Proofs.Exit.stepState visit.outcome).construction.events =
        (Goose.Proofs.Exit.stepState (evalValue 40 config environment expression ready)).construction.events) ∧
    after.construction.events = [.begin 0, .write 0 0, .write 0 1, .publish 0] ∧
    ∃ final, runModule 40 config .initial = .ok () final ∧ final.construction.events = after.construction.events := by
  let after := stepState (globalInitializer 40 config 0 .initial)
  have actual : globalInitializer 40 config 0 .initial = .ok () after := by
    unfold after stepState globalInitializer config context implementation global expression
    unfold evalValue
    cbv
    unfold evalValue
    cbv
  have events : after.construction.events = [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
    unfold after stepState globalInitializer config context implementation global expression
    unfold evalValue
    cbv
    unfold evalValue
    cbv
  let visit : Invocation Goose.Core.GlobalId Unit := ⟨0, 0, .initial, .ok () after⟩
  have replay : OperandReplay (globalInitializer 40 config) 0 [0] [] .initial (.ok [()] after) [visit] :=
    .next actual (.done 1 [()] after)
  obtain ⟨history, initial, final, retained⟩ := fixedGlobal_visit_sourceEvents replay closed visit (by simp [visit])
    global rfl rfl expressionSyntax
  refine ⟨after, [visit], replay, ⟨visit, by simp, history, final⟩, events,
    stepState (runModule 40 config .initial), ?_, ?_⟩
  · unfold stepState config context implementation global expression
    cbv
    unfold evalValue
    cbv
  · rw [events]
    unfold stepState config context implementation global expression
    cbv
    unfold evalValue
    cbv

#print axioms fixedGlobal_sourceEvents
end Goose.Proofs.ConstructionGhostFixedGlobalEventsWitness

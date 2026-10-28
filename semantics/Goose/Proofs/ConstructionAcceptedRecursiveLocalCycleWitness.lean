import Goose.Proofs.ConstructionAcceptedRecursiveLocalCallModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

private def localCycleSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def localCycleEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, localCycleSummary⟩
private def localCycleHelper : Impl := ⟨"cycle", #[], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [.letS 0 (.lit .i64 3) 0] (some (.call 1 [] 0)), localCycleSummary⟩
private def localCycleModule : Module := ⟨#["local-cycle.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩], #[localCycleEntry, localCycleHelper],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "cycle", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def localCycleConfig : EvalConfig := ⟨.release, localCycleModule⟩

theorem localCycle_validated : validate localCycleModule = .ok () := by cbv

theorem localCycle_graph : RegisterCallGraphWithLocals localCycleConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [localCycleConfig, localCycleModule] at contextAt
    subst context
    simp [localCycleConfig, localCycleModule] at implementationAt
    subst implementation
    simp [localCycleEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [localCycleConfig, localCycleModule] at contextAt
      subst context
      simp [localCycleConfig, localCycleModule] at implementationAt
      subst implementation
      refine ⟨_, rfl, Or.inr ⟨0, _, 1, 0, ⟨1, "cycle", [], [[]], []⟩, localCycleHelper, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩⟩
      · repeat constructor
      · intro id expression origin member descriptor found
        simp [localCycleHelper] at member found
        obtain ⟨rfl, rfl, rfl⟩ := member
        simp at found
        subst descriptor
        exact Or.inl ⟨.i64, rfl⟩
    | succ target => simp [localCycleConfig, localCycleModule] at contextAt

private def localCycleStops : Bool :=
  match runModule 20 localCycleConfig .initial with
  | .stop .timeout _ => true
  | _ => false

theorem localCycle_timeout : localCycleStops = true := by decide +kernel

theorem localCycle_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld localCycleConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel localCycleConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel localCycleConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩
  let calleeContext : Context := ⟨1, "cycle", [], [[]], []⟩
  let entryContext : Context := ⟨0, "entry", [], [], []⟩
  apply acceptedLocalCallModule_allFuel fuel localCycleConfig (acceptedModule localCycleConfig localCycle_validated)
    descriptor 1 0 calleeContext localCycleHelper (by rfl) (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    (by rfl) (by rfl) (by rfl) (by rfl) localCycle_graph entryContext localCycleEntry (by rfl) (by rfl)
  · exact .nil
  · simp [localCycleEntry, Block.stmts]
  · simp [localCycleEntry, Block.stmts]
  · simp [localCycleEntry, Block.stmts]
  · simp [localCycleEntry, Block.stmts]
  · rfl

#print axioms localCycle_allFuel
#print axioms localCycle_timeout
#print axioms localCycle_graph
#print axioms localCycle_validated
end Goose.Proofs.ConstructionAcceptedExecution

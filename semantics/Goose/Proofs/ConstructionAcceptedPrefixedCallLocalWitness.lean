import Goose.Proofs.ConstructionAcceptedCallLocalGraphModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

private def prefixedCycleSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def prefixedCycleEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, prefixedCycleSummary⟩
private def prefixedCycleHelper : Impl := ⟨"cycle", #[], #[⟨.int .i64, .register, none⟩],
  #[⟨"first", .int .i64, .immutable, 0, 0⟩, ⟨"second", .int .i64, .immutable, 0, 0⟩],
  .mk 0 [.letS 0 (.lit .i64 3) 0, .letS 1 (.call 1 [] 0) 0] (some (.read (.var 1))), prefixedCycleSummary⟩
private def prefixedCycleModule : Module := ⟨#["prefixed-local-cycle.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩], #[prefixedCycleEntry, prefixedCycleHelper],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "cycle", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def prefixedCycleConfig : EvalConfig := ⟨.release, prefixedCycleModule⟩

theorem prefixedCycle_validated : validate prefixedCycleModule = .ok () := by cbv

theorem prefixedCycle_graph : RegisterCallGraphWithCallLocals prefixedCycleConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [prefixedCycleConfig, prefixedCycleModule] at contextAt
    subst context
    simp [prefixedCycleConfig, prefixedCycleModule] at implementationAt
    subst implementation
    simp [prefixedCycleEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [prefixedCycleConfig, prefixedCycleModule] at contextAt
      subst context
      simp [prefixedCycleConfig, prefixedCycleModule] at implementationAt
      subst implementation
      apply Or.inr
      refine ⟨_, 0, 1, 1, 0, 0, [.letS 0 (.lit .i64 3) 0], [], .read (.var 1),
        ⟨1, "cycle", [], [[]], []⟩, prefixedCycleHelper, rfl, rfl, ?_, .nil, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
      · repeat constructor
      · repeat constructor
      · intro id expression origin member descriptor found
        simp at member
        obtain ⟨rfl, rfl, rfl⟩ := member
        simp [prefixedCycleHelper] at found
        subst descriptor
        exact Or.inl ⟨.i64, rfl⟩
      · intro descriptor found
        simp [prefixedCycleHelper] at found
        subst descriptor
        exact Or.inl ⟨.i64, rfl⟩
      · intro id expression origin member
        cases member
    | succ target => simp [prefixedCycleConfig, prefixedCycleModule] at contextAt

private def prefixedCycleStops : Bool :=
  match runModule 25 prefixedCycleConfig .initial with
  | .stop .timeout _ => true
  | _ => false

theorem prefixedCycle_timeout : prefixedCycleStops = true := by decide +kernel

theorem prefixedCycle_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld prefixedCycleConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel prefixedCycleConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel prefixedCycleConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩
  let context : Context := ⟨1, "cycle", [], [[]], []⟩
  apply acceptedCallLocalGraphModule_allFuel fuel prefixedCycleConfig (acceptedModule prefixedCycleConfig prefixedCycle_validated)
    descriptor 1 0 context prefixedCycleHelper (by rfl) (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    (by rfl) (by rfl) (by rfl) (by rfl) prefixedCycle_graph ⟨0, "entry", [], [], []⟩ prefixedCycleEntry (by rfl) (by rfl)
  · exact .nil
  · simp [prefixedCycleEntry, Block.stmts]
  · simp [prefixedCycleEntry, Block.stmts]
  · simp [prefixedCycleEntry, Block.stmts]
  · simp [prefixedCycleEntry, Block.stmts]
  · rfl

#print axioms prefixedCycle_allFuel
#print axioms prefixedCycle_timeout
#print axioms prefixedCycle_graph
#print axioms prefixedCycle_validated
end Goose.Proofs.ConstructionAcceptedExecution

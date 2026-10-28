import Goose.Proofs.ConstructionAcceptedCallLocalGraphModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def callLocalCycleSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def callLocalCycleEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, callLocalCycleSummary⟩
private def callLocalCycleHelper : Impl := ⟨"cycle", #[], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [.letS 0 (.call 1 [] 0) 0] (some (.read (.var 0))), callLocalCycleSummary⟩
private def callLocalCycleModule : Module := ⟨#["local-call-cycle.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩], #[callLocalCycleEntry, callLocalCycleHelper],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "cycle", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def callLocalCycleConfig : EvalConfig := ⟨.release, callLocalCycleModule⟩

theorem callLocalCycle_validated : validate callLocalCycleModule = .ok () := by cbv

theorem callLocalCycle_graph : RegisterCallGraphWithCallLocals callLocalCycleConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [callLocalCycleConfig, callLocalCycleModule] at contextAt
    subst context
    simp [callLocalCycleConfig, callLocalCycleModule] at implementationAt
    subst implementation
    simp [callLocalCycleEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [callLocalCycleConfig, callLocalCycleModule] at contextAt
      subst context
      simp [callLocalCycleConfig, callLocalCycleModule] at implementationAt
      subst implementation
      apply Or.inr
      refine ⟨_, 0, [.letS 0 (.call 1 [] 0) 0], .read (.var 0), rfl, rfl, ?_, ?_, ?_⟩
      · exact .call 0 1 0 0 [] ⟨1, "cycle", [], [[]], []⟩ callLocalCycleHelper rfl rfl rfl rfl .nil
      · repeat constructor
      · intro id expression origin member descriptor found
        simp at member
        obtain ⟨rfl, rfl, rfl⟩ := member
        simp [callLocalCycleHelper] at found
        subst descriptor
        exact Or.inl ⟨.i64, rfl⟩
    | succ target => simp [callLocalCycleConfig, callLocalCycleModule] at contextAt

private def callLocalCycleStops : Bool :=
  match runModule 20 callLocalCycleConfig .initial with
  | .stop .timeout _ => true
  | _ => false

theorem callLocalCycle_timeout : callLocalCycleStops = true := by decide +kernel

theorem callLocalCycle_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld callLocalCycleConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel callLocalCycleConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel callLocalCycleConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩
  let context : Context := ⟨1, "cycle", [], [[]], []⟩
  apply acceptedCallLocalGraphModule_allFuel fuel callLocalCycleConfig (acceptedModule callLocalCycleConfig callLocalCycle_validated)
    descriptor 1 0 context callLocalCycleHelper (by rfl) (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    (by rfl) (by rfl) (by rfl) (by rfl) callLocalCycle_graph ⟨0, "entry", [], [], []⟩ callLocalCycleEntry (by rfl) (by rfl)
  · exact .nil
  · simp [callLocalCycleEntry, Block.stmts]
  · simp [callLocalCycleEntry, Block.stmts]
  · simp [callLocalCycleEntry, Block.stmts]
  · simp [callLocalCycleEntry, Block.stmts]
  · rfl

#print axioms callLocalCycle_allFuel
#print axioms callLocalCycle_timeout
#print axioms callLocalCycle_graph
#print axioms callLocalCycle_validated
end Goose.Proofs.ConstructionAcceptedExecution

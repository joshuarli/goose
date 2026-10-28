import Goose.Proofs.ConstructionAcceptedRecursiveMixedGlobalModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

private def cycleSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def cycleEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, cycleSummary⟩
private def cycleHelper : Impl := ⟨"cycle", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.call 1 [] 0)), cycleSummary⟩
private def cycleModule : Module := ⟨#["cycle.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩], #[cycleEntry, cycleHelper],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "cycle", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def cycleConfig : EvalConfig := ⟨.release, cycleModule⟩

theorem cycle_validated : validate cycleModule = .ok () := by cbv

theorem cycle_graph : RegisterCallGraph cycleConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [cycleConfig, cycleModule] at contextAt
    subst context
    simp [cycleConfig, cycleModule] at implementationAt
    subst implementation
    simp [cycleEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [cycleConfig, cycleModule] at contextAt
      subst context
      simp [cycleConfig, cycleModule] at implementationAt
      subst implementation
      exact ⟨_, rfl, Or.inr ⟨0, 1, 0, ⟨1, "cycle", [], [[]], []⟩, cycleHelper, rfl, rfl, rfl, rfl, rfl⟩⟩
    | succ target => simp [cycleConfig, cycleModule] at contextAt

private def cycleStops : Bool :=
  match runModule 20 cycleConfig .initial with
  | .stop .timeout _ => true
  | _ => false

theorem cycle_timeout : cycleStops = true := by decide +kernel

theorem cycle_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld cycleConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel cycleConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel cycleConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  have scalars : FlatGlobalsAreScalar cycleConfig := by
    intro id descriptor declared flat
    cases id with
    | zero =>
      have same : descriptor = ⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩ := by
        simpa [cycleConfig, cycleModule] using declared.symm
      subst descriptor
      exact Or.inl ⟨.i64, rfl⟩
    | succ id => simp [cycleConfig, cycleModule] at declared
  apply acceptedRecursiveMixedGlobalModule_allFuel fuel cycleConfig (acceptedModule cycleConfig cycle_validated)
    scalars ⟨0, "entry", [], [], []⟩ cycleEntry
  · intro id inside
    change id < 1 at inside
    cases id with
    | zero => exact ⟨_, rfl, Or.inr ⟨1, 0, ⟨1, "cycle", [], [[]], []⟩, cycleHelper,
        rfl, Or.inl ⟨.i64, rfl⟩, rfl, rfl, rfl, rfl, cycle_graph⟩⟩
    | succ id => omega
  · rfl
  · rfl
  · exact .nil
  · simp [cycleEntry, Block.stmts]
  · simp [cycleEntry, Block.stmts]
  · simp [cycleEntry, Block.stmts]
  · simp [cycleEntry, Block.stmts]
  · rfl

#print axioms cycle_allFuel
#print axioms cycle_timeout
#print axioms cycle_validated
#print axioms cycle_graph
end Goose.Proofs.ConstructionAcceptedExecution

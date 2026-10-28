import Goose.Proofs.ConstructionAcceptedDependentGlobalModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def dependentGlobalWitnessEntry : Impl :=
  ⟨"entry", #[], #[], #[], .mk 0 [.assign (.global 1) (.lit .i64 9) 0] none, .unknown⟩

private def dependentGlobalWitnessModule : Module :=
  ⟨#["scalar-global.goose"], #[.int .i64, .varr (.int .u8)],
    #[⟨"source", .int .i64, .immutable, .lit .i64 1, 0⟩,
      ⟨"count", .int .i64, .mutable, .read (.global 0), 0⟩,
      ⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [65] 0, 0⟩],
    #[dependentGlobalWitnessEntry], #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 1, "assign"⟩], #[], #[]⟩

private def dependentGlobalWitnessConfig : EvalConfig := ⟨.release, dependentGlobalWitnessModule⟩

theorem dependentGlobalWitness_validated : validate dependentGlobalWitnessModule = .ok () := by cbv

private def dependentGlobalWitnessObservation : Option Int :=
  match runModule 100 dependentGlobalWitnessConfig .initial with
  | .ok () state => match state.objects.lookup (.global 1) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem dependentGlobalWitness_assignment : dependentGlobalWitnessObservation = some 9 := by decide +kernel

private def dependentGlobalPrefixObservation : Option Int :=
  match initGlobals 100 dependentGlobalWitnessConfig [0, 1] .initial with
  | .ok () state => match state.objects.lookup (.global 1) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem dependentGlobalWitness_initializer : dependentGlobalPrefixObservation = some 1 := by decide +kernel

theorem dependentGlobalWitness_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld dependentGlobalWitnessConfig initialized
        (Goose.Proofs.Exit.stepState (runModule fuel dependentGlobalWitnessConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel dependentGlobalWitnessConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  apply acceptedDependentGlobalModule_allFuel fuel dependentGlobalWitnessConfig
    (acceptedModule dependentGlobalWitnessConfig dependentGlobalWitness_validated)
    ⟨0, "entry", [], [], []⟩ dependentGlobalWitnessEntry
  · intro id inside
    change id < 3 at inside
    cases id with
    | zero =>
      exact ⟨_, rfl, Or.inl (Or.inl (.integer .i64 1 rfl rfl))⟩
    | succ id =>
      cases id with
      | zero => exact ⟨_, rfl, Or.inr ⟨0, _, by omega, rfl, rfl, rfl, Or.inl ⟨.i64, rfl⟩⟩⟩
      | succ id =>
        cases id with
        | zero => exact ⟨_, rfl, Or.inl (Or.inr ⟨[65], 0, rfl, rfl⟩)⟩
        | succ id => omega
  · rfl
  · rfl
  · exact .assign (.global 1) (.lit .i64 9) 0 [] (.numeric (.scalar (.scalar (.integer .i64 9))))
      (Or.inr ⟨1, rfl⟩) .nil
  · intro declaration member
    simp [dependentGlobalWitnessEntry, Block.stmts, ByteOwnerDeclaration.statement] at member
  · intro id expression origin member
    simp [dependentGlobalWitnessEntry, Block.stmts] at member
  · intro id expression origin member
    simp [dependentGlobalWitnessEntry, Block.stmts] at member
  · intro id expression origin member descriptor declared
    simp [dependentGlobalWitnessEntry, Block.stmts] at member
    obtain ⟨idEq, expressionEq, originEq⟩ := member
    subst id
    have same : descriptor = ⟨"count", .int .i64, .mutable, .read (.global 0), 0⟩ := by
      simpa [dependentGlobalWitnessConfig, dependentGlobalWitnessModule] using declared.symm
    subst descriptor
    exact Or.inl ⟨.i64, rfl⟩
  · rfl

#print axioms dependentGlobalWitness_initializer
#print axioms dependentGlobalWitness_allFuel
#print axioms dependentGlobalWitness_validated
#print axioms dependentGlobalWitness_assignment
end Goose.Proofs.ConstructionAcceptedExecution

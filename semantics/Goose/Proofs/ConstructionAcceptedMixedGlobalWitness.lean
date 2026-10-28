import Goose.Proofs.ConstructionAcceptedMixedGlobalModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def mixedGlobalWitnessEntry : Impl :=
  ⟨"entry", #[], #[], #[], .mk 0 [.assign (.global 0) (.lit .i64 9) 0] none, .unknown⟩

private def mixedGlobalWitnessModule : Module :=
  ⟨#["scalar-global.goose"], #[.int .i64, .varr (.int .u8)],
    #[⟨"count", .int .i64, .mutable, .lit .i64 1, 0⟩,
      ⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [65] 0, 0⟩],
    #[mixedGlobalWitnessEntry], #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 1, "assign"⟩], #[], #[]⟩

private def mixedGlobalWitnessConfig : EvalConfig := ⟨.release, mixedGlobalWitnessModule⟩

theorem mixedGlobalWitness_validated : validate mixedGlobalWitnessModule = .ok () := by cbv

private def mixedGlobalWitnessObservation : Option Int :=
  match runModule 100 mixedGlobalWitnessConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem mixedGlobalWitness_assignment : mixedGlobalWitnessObservation = some 9 := by decide +kernel

theorem mixedGlobalWitness_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld mixedGlobalWitnessConfig initialized
        (Goose.Proofs.Exit.stepState (runModule fuel mixedGlobalWitnessConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel mixedGlobalWitnessConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  apply acceptedMixedGlobalModule_allFuel fuel mixedGlobalWitnessConfig
    (acceptedModule mixedGlobalWitnessConfig mixedGlobalWitness_validated)
    ⟨0, "entry", [], [], []⟩ mixedGlobalWitnessEntry
  · intro id inside
    change id < 2 at inside
    cases id with
    | zero =>
      refine ⟨_, rfl, Or.inl (.integer .i64 1 rfl rfl)⟩
    | succ id =>
      cases id with
      | zero => exact ⟨_, rfl, Or.inr ⟨[65], 0, rfl, rfl⟩⟩
      | succ id => omega
  · rfl
  · rfl
  · exact .assign (.global 0) (.lit .i64 9) 0 [] (.numeric (.scalar (.scalar (.integer .i64 9))))
      (Or.inr ⟨0, rfl⟩) .nil
  · intro declaration member
    simp [mixedGlobalWitnessEntry, Block.stmts, ByteOwnerDeclaration.statement] at member
  · intro id expression origin member
    simp [mixedGlobalWitnessEntry, Block.stmts] at member
  · intro id expression origin member
    simp [mixedGlobalWitnessEntry, Block.stmts] at member
  · intro id expression origin member descriptor declared
    simp [mixedGlobalWitnessEntry, Block.stmts] at member
    obtain ⟨idEq, expressionEq, originEq⟩ := member
    subst id
    have same : descriptor = ⟨"count", .int .i64, .mutable, .lit .i64 1, 0⟩ := by
      simpa [mixedGlobalWitnessConfig, mixedGlobalWitnessModule] using declared.symm
    subst descriptor
    exact Or.inl ⟨.i64, rfl⟩
  · rfl

#print axioms mixedGlobalWitness_allFuel
#print axioms mixedGlobalWitness_validated
#print axioms mixedGlobalWitness_assignment
end Goose.Proofs.ConstructionAcceptedExecution

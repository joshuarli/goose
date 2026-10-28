import Goose.Proofs.ConstructionAcceptedConditionalGlobalModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def conditionalGlobalWitnessEntry : Impl :=
  ⟨"entry", #[], #[], #[], .mk 0 [.assign (.global 1) (.lit .i64 9) 0] none, .unknown⟩

private def conditionalGlobalWitnessModule : Module :=
  ⟨#["scalar-global.goose"], #[.int .i64, .varr (.int .u8)],
    #[⟨"source", .int .i64, .immutable, .lit .i64 1, 0⟩,
      ⟨"count", .int .i64, .mutable, .ifE (.bool true) (.mk 0 [] (some (.lit .i64 3))) (.mk 1 [] (some (.lit .i64 4))) 0, 0⟩,
      ⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [65] 0, 0⟩],
    #[conditionalGlobalWitnessEntry], #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 1, "assign"⟩], #[], #[]⟩

private def conditionalGlobalWitnessConfig : EvalConfig := ⟨.release, conditionalGlobalWitnessModule⟩

theorem conditionalGlobalWitness_validated : validate conditionalGlobalWitnessModule = .ok () := by cbv

private def conditionalGlobalWitnessObservation : Option Int :=
  match runModule 100 conditionalGlobalWitnessConfig .initial with
  | .ok () state => match state.objects.lookup (.global 1) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem conditionalGlobalWitness_assignment : conditionalGlobalWitnessObservation = some 9 := by decide +kernel

private def conditionalGlobalPrefixObservation : Option Int :=
  match initGlobals 100 conditionalGlobalWitnessConfig [0, 1] .initial with
  | .ok () state => match state.objects.lookup (.global 1) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem conditionalGlobalWitness_initializer : conditionalGlobalPrefixObservation = some 3 := by decide +kernel

theorem conditionalGlobalWitness_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld conditionalGlobalWitnessConfig initialized
        (Goose.Proofs.Exit.stepState (runModule fuel conditionalGlobalWitnessConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel conditionalGlobalWitnessConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  apply acceptedConditionalGlobalModule_allFuel fuel conditionalGlobalWitnessConfig
    (acceptedModule conditionalGlobalWitnessConfig conditionalGlobalWitness_validated)
    ⟨0, "entry", [], [], []⟩ conditionalGlobalWitnessEntry
  · intro id inside
    change id < 3 at inside
    cases id with
    | zero =>
      exact ⟨_, rfl, Or.inl (Or.inl ⟨.numeric (.scalar (.scalar (.integer .i64 1))), Or.inl ⟨.i64, rfl⟩⟩)⟩
    | succ id =>
      cases id with
      | zero => exact ⟨_, rfl, Or.inr (.integer true 0 1 .i64 3 4 0 rfl rfl)⟩
      | succ id =>
        cases id with
        | zero => exact ⟨_, rfl, Or.inl (Or.inr ⟨[65], 0, rfl, rfl⟩)⟩
        | succ id => omega
  · rfl
  · rfl
  · exact .assign (.global 1) (.lit .i64 9) 0 [] (.numeric (.scalar (.scalar (.integer .i64 9))))
      (Or.inr ⟨1, rfl⟩) .nil
  · intro declaration member
    simp [conditionalGlobalWitnessEntry, Block.stmts, ByteOwnerDeclaration.statement] at member
  · intro id expression origin member
    simp [conditionalGlobalWitnessEntry, Block.stmts] at member
  · intro id expression origin member
    simp [conditionalGlobalWitnessEntry, Block.stmts] at member
  · intro id expression origin member descriptor declared
    simp [conditionalGlobalWitnessEntry, Block.stmts] at member
    obtain ⟨idEq, expressionEq, originEq⟩ := member
    subst id
    have same : descriptor = ⟨"count", .int .i64, .mutable, .ifE (.bool true) (.mk 0 [] (some (.lit .i64 3))) (.mk 1 [] (some (.lit .i64 4))) 0, 0⟩ := by
      simpa [conditionalGlobalWitnessConfig, conditionalGlobalWitnessModule] using declared.symm
    subst descriptor
    exact Or.inl ⟨.i64, rfl⟩
  · rfl

#print axioms conditionalGlobalWitness_initializer
#print axioms conditionalGlobalWitness_allFuel
#print axioms conditionalGlobalWitness_validated
#print axioms conditionalGlobalWitness_assignment
end Goose.Proofs.ConstructionAcceptedExecution

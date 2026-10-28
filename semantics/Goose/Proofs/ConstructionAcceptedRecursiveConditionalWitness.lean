import Goose.Proofs.ConstructionAcceptedRecursiveConditionalModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def recursiveConditionalWitnessEntry : Impl :=
  ⟨"entry", #[], #[], #[], .mk 0 [.assign (.global 1) (.lit .i64 9) 0] none, .unknown⟩

private def recursiveConditionalWitnessModule : Module :=
  ⟨#["scalar-global.goose"], #[.int .i64, .varr (.int .u8)],
    #[⟨"source", .int .i64, .immutable, .lit .i64 1, 0⟩,
      ⟨"count", .int .i64, .mutable, .ifE (.cmp .lt (.read (.global 0)) (.lit .i64 2)) (.mk 0 [] (some (.bin .add (.read (.global 0)) (.lit .i64 2) 0))) (.mk 1 [] (some (.lit .i64 4))) 0, 0⟩,
      ⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [65] 0, 0⟩],
    #[recursiveConditionalWitnessEntry], #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 1, "assign"⟩], #[], #[]⟩

private def recursiveConditionalWitnessConfig : EvalConfig := ⟨.release, recursiveConditionalWitnessModule⟩

theorem recursiveConditionalWitness_validated : validate recursiveConditionalWitnessModule = .ok () := by cbv

private def recursiveConditionalWitnessObservation : Option Int :=
  match runModule 100 recursiveConditionalWitnessConfig .initial with
  | .ok () state => match state.objects.lookup (.global 1) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem recursiveConditionalWitness_assignment : recursiveConditionalWitnessObservation = some 9 := by decide +kernel

private def recursiveConditionalPrefixObservation : Option Int :=
  match initGlobals 100 recursiveConditionalWitnessConfig [0, 1] .initial with
  | .ok () state => match state.objects.lookup (.global 1) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem recursiveConditionalWitness_initializer : recursiveConditionalPrefixObservation = some 3 := by decide +kernel

theorem recursiveConditionalWitness_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld recursiveConditionalWitnessConfig initialized
        (Goose.Proofs.Exit.stepState (runModule fuel recursiveConditionalWitnessConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel recursiveConditionalWitnessConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  apply acceptedRecursiveConditionalModule_allFuel fuel recursiveConditionalWitnessConfig
    (acceptedModule recursiveConditionalWitnessConfig recursiveConditionalWitness_validated)
    ⟨0, "entry", [], [], []⟩ recursiveConditionalWitnessEntry
  · intro id inside
    change id < 3 at inside
    cases id with
    | zero =>
      exact ⟨_, rfl, Or.inl (Or.inl (Or.inl ⟨.numeric (.scalar (.scalar (.integer .i64 1))), Or.inl ⟨.i64, rfl⟩⟩))⟩
    | succ id =>
      cases id with
      | zero => exact ⟨_, rfl, Or.inr ⟨_, _, _, 0, 1, 0, rfl,
        .comparison .lt (.numeric (.scalar (.scalar (.globalRead 0)))) (.numeric (.scalar (.scalar (.integer .i64 2)))),
        .binary .add 0 (.numeric (.scalar (.scalar (.globalRead 0)))) (.numeric (.scalar (.scalar (.integer .i64 2)))),
        .numeric (.scalar (.scalar (.integer .i64 4))), Or.inl ⟨.i64, rfl⟩⟩⟩
      | succ id =>
        cases id with
        | zero => exact ⟨_, rfl, Or.inl (Or.inl (Or.inr ⟨[65], 0, rfl, rfl⟩))⟩
        | succ id => omega
  · rfl
  · rfl
  · exact .assign (.global 1) (.lit .i64 9) 0 [] (.numeric (.scalar (.scalar (.integer .i64 9))))
      (Or.inr ⟨1, rfl⟩) .nil
  · intro declaration member
    simp [recursiveConditionalWitnessEntry, Block.stmts, ByteOwnerDeclaration.statement] at member
  · intro id expression origin member
    simp [recursiveConditionalWitnessEntry, Block.stmts] at member
  · intro id expression origin member
    simp [recursiveConditionalWitnessEntry, Block.stmts] at member
  · intro id expression origin member descriptor declared
    simp [recursiveConditionalWitnessEntry, Block.stmts] at member
    obtain ⟨idEq, expressionEq, originEq⟩ := member
    subst id
    have same : descriptor = ⟨"count", .int .i64, .mutable, .ifE (.cmp .lt (.read (.global 0)) (.lit .i64 2)) (.mk 0 [] (some (.bin .add (.read (.global 0)) (.lit .i64 2) 0))) (.mk 1 [] (some (.lit .i64 4))) 0, 0⟩ := by
      simpa [recursiveConditionalWitnessConfig, recursiveConditionalWitnessModule] using declared.symm
    subst descriptor
    exact Or.inl ⟨.i64, rfl⟩
  · rfl

#print axioms recursiveConditionalWitness_initializer
#print axioms recursiveConditionalWitness_allFuel
#print axioms recursiveConditionalWitness_validated
#print axioms recursiveConditionalWitness_assignment
end Goose.Proofs.ConstructionAcceptedExecution

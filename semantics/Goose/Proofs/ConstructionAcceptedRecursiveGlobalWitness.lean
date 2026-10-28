import Goose.Proofs.ConstructionAcceptedRecursiveGlobalModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def recursiveGlobalWitnessEntry : Impl :=
  ⟨"entry", #[], #[], #[], .mk 0 [.assign (.global 1) (.lit .i64 9) 0] none, .unknown⟩

private def recursiveGlobalWitnessModule : Module :=
  ⟨#["scalar-global.goose"], #[.int .i64, .varr (.int .u8)],
    #[⟨"source", .int .i64, .immutable, .lit .i64 1, 0⟩,
      ⟨"count", .int .i64, .mutable, .bin .add (.read (.global 0)) (.lit .i64 2) 0, 0⟩,
      ⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [65] 0, 0⟩],
    #[recursiveGlobalWitnessEntry], #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 1, "assign"⟩], #[], #[]⟩

private def recursiveGlobalWitnessConfig : EvalConfig := ⟨.release, recursiveGlobalWitnessModule⟩

theorem recursiveGlobalWitness_validated : validate recursiveGlobalWitnessModule = .ok () := by cbv

private def recursiveGlobalWitnessObservation : Option Int :=
  match runModule 100 recursiveGlobalWitnessConfig .initial with
  | .ok () state => match state.objects.lookup (.global 1) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem recursiveGlobalWitness_assignment : recursiveGlobalWitnessObservation = some 9 := by decide +kernel

private def recursiveGlobalPrefixObservation : Option Int :=
  match initGlobals 100 recursiveGlobalWitnessConfig [0, 1] .initial with
  | .ok () state => match state.objects.lookup (.global 1) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem recursiveGlobalWitness_initializer : recursiveGlobalPrefixObservation = some 3 := by decide +kernel

theorem recursiveGlobalWitness_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld recursiveGlobalWitnessConfig initialized
        (Goose.Proofs.Exit.stepState (runModule fuel recursiveGlobalWitnessConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel recursiveGlobalWitnessConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  apply acceptedRecursiveGlobalModule_allFuel fuel recursiveGlobalWitnessConfig
    (acceptedModule recursiveGlobalWitnessConfig recursiveGlobalWitness_validated)
    ⟨0, "entry", [], [], []⟩ recursiveGlobalWitnessEntry
  · intro id inside
    change id < 3 at inside
    cases id with
    | zero =>
      exact ⟨_, rfl, Or.inl ⟨.numeric (.scalar (.scalar (.integer .i64 1))), Or.inl ⟨.i64, rfl⟩⟩⟩
    | succ id =>
      cases id with
      | zero => exact ⟨_, rfl, Or.inl ⟨.binary .add 0 (.numeric (.scalar (.scalar (.globalRead 0))))
        (.numeric (.scalar (.scalar (.integer .i64 2)))), Or.inl ⟨.i64, rfl⟩⟩⟩
      | succ id =>
        cases id with
        | zero => exact ⟨_, rfl, Or.inr ⟨[65], 0, rfl, rfl⟩⟩
        | succ id => omega
  · rfl
  · rfl
  · exact .assign (.global 1) (.lit .i64 9) 0 [] (.numeric (.scalar (.scalar (.integer .i64 9))))
      (Or.inr ⟨1, rfl⟩) .nil
  · intro declaration member
    simp [recursiveGlobalWitnessEntry, Block.stmts, ByteOwnerDeclaration.statement] at member
  · intro id expression origin member
    simp [recursiveGlobalWitnessEntry, Block.stmts] at member
  · intro id expression origin member
    simp [recursiveGlobalWitnessEntry, Block.stmts] at member
  · intro id expression origin member descriptor declared
    simp [recursiveGlobalWitnessEntry, Block.stmts] at member
    obtain ⟨idEq, expressionEq, originEq⟩ := member
    subst id
    have same : descriptor = ⟨"count", .int .i64, .mutable, .bin .add (.read (.global 0)) (.lit .i64 2) 0, 0⟩ := by
      simpa [recursiveGlobalWitnessConfig, recursiveGlobalWitnessModule] using declared.symm
    subst descriptor
    exact Or.inl ⟨.i64, rfl⟩
  · rfl

#print axioms recursiveGlobalWitness_initializer
#print axioms recursiveGlobalWitness_allFuel
#print axioms recursiveGlobalWitness_validated
#print axioms recursiveGlobalWitness_assignment
end Goose.Proofs.ConstructionAcceptedExecution

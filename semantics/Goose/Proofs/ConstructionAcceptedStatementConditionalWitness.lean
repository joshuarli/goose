import Goose.Proofs.ConstructionAcceptedStatementConditionalModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def statementConditionalWitnessEntry : Impl :=
  ⟨"entry", #[], #[], #[], .mk 0 [.assign (.global 1) (.lit .i64 9) 0] none, .unknown⟩

private def statementConditionalWitnessModule : Module :=
  ⟨#["scalar-global.goose"], #[.int .i64, .varr (.int .u8)],
    #[⟨"source", .int .i64, .immutable, .lit .i64 1, 0⟩,
      ⟨"count", .int .i64, .mutable, .ifE (.cmp .lt (.read (.global 0)) (.lit .i64 2)) (.mk 0 [.expr (.read (.global 0)) 0, .expr (.bin .add (.read (.global 0)) (.lit .i64 2) 0) 0] (some (.bin .add (.read (.global 0)) (.lit .i64 2) 0))) (.mk 1 [.expr (.bool false) 0] (some (.lit .i64 4))) 0, 0⟩,
      ⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [65] 0, 0⟩],
    #[statementConditionalWitnessEntry], #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 1, "assign"⟩], #[], #[]⟩

private def statementConditionalWitnessConfig : EvalConfig := ⟨.release, statementConditionalWitnessModule⟩

theorem statementConditionalWitness_validated : validate statementConditionalWitnessModule = .ok () := by cbv

private def statementConditionalWitnessObservation : Option Int :=
  match runModule 100 statementConditionalWitnessConfig .initial with
  | .ok () state => match state.objects.lookup (.global 1) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem statementConditionalWitness_assignment : statementConditionalWitnessObservation = some 9 := by decide +kernel

private def statementConditionalPrefixObservation : Option Int :=
  match initGlobals 100 statementConditionalWitnessConfig [0, 1] .initial with
  | .ok () state => match state.objects.lookup (.global 1) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem statementConditionalWitness_initializer : statementConditionalPrefixObservation = some 3 := by decide +kernel

theorem statementConditionalWitness_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld statementConditionalWitnessConfig initialized
        (Goose.Proofs.Exit.stepState (runModule fuel statementConditionalWitnessConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel statementConditionalWitnessConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  apply acceptedStatementConditionalModule_allFuel fuel statementConditionalWitnessConfig
    (acceptedModule statementConditionalWitnessConfig statementConditionalWitness_validated)
    ⟨0, "entry", [], [], []⟩ statementConditionalWitnessEntry
  · intro id inside
    change id < 3 at inside
    cases id with
    | zero =>
      exact ⟨_, rfl, Or.inl (Or.inl (Or.inl (Or.inl ⟨.numeric (.scalar (.scalar (.integer .i64 1))), Or.inl ⟨.i64, rfl⟩⟩)))⟩
    | succ id =>
      cases id with
      | zero => exact ⟨_, rfl, Or.inr ⟨_, _, _, _, _, 0, 1, 0, rfl,
        .comparison .lt (.numeric (.scalar (.scalar (.globalRead 0)))) (.numeric (.scalar (.scalar (.integer .i64 2)))),
        .binary .add 0 (.numeric (.scalar (.scalar (.globalRead 0)))) (.numeric (.scalar (.scalar (.integer .i64 2)))),
        .numeric (.scalar (.scalar (.integer .i64 4))),
        .cons _ 0 _ (.numeric (.scalar (.scalar (.globalRead 0))))
          (.cons _ 0 _ (.binary .add 0 (.numeric (.scalar (.scalar (.globalRead 0))))
            (.numeric (.scalar (.scalar (.integer .i64 2))))) .nil),
        .cons _ 0 _ (.numeric (.scalar (.scalar (.boolean false)))) .nil, Or.inl ⟨.i64, rfl⟩⟩⟩
      | succ id =>
        cases id with
        | zero => exact ⟨_, rfl, Or.inl (Or.inl (Or.inl (Or.inr ⟨[65], 0, rfl, rfl⟩)))⟩
        | succ id => omega
  · rfl
  · rfl
  · exact .assign (.global 1) (.lit .i64 9) 0 [] (.numeric (.scalar (.scalar (.integer .i64 9))))
      (Or.inr ⟨1, rfl⟩) .nil
  · intro declaration member
    simp [statementConditionalWitnessEntry, Block.stmts, ByteOwnerDeclaration.statement] at member
  · intro id expression origin member
    simp [statementConditionalWitnessEntry, Block.stmts] at member
  · intro id expression origin member
    simp [statementConditionalWitnessEntry, Block.stmts] at member
  · intro id expression origin member descriptor declared
    simp [statementConditionalWitnessEntry, Block.stmts] at member
    obtain ⟨idEq, expressionEq, originEq⟩ := member
    subst id
    have same : descriptor = ⟨"count", .int .i64, .mutable, .ifE (.cmp .lt (.read (.global 0)) (.lit .i64 2)) (.mk 0 [.expr (.read (.global 0)) 0, .expr (.bin .add (.read (.global 0)) (.lit .i64 2) 0) 0] (some (.bin .add (.read (.global 0)) (.lit .i64 2) 0))) (.mk 1 [.expr (.bool false) 0] (some (.lit .i64 4))) 0, 0⟩ := by
      simpa [statementConditionalWitnessConfig, statementConditionalWitnessModule] using declared.symm
    subst descriptor
    exact Or.inl ⟨.i64, rfl⟩
  · rfl

#print axioms statementConditionalWitness_initializer
#print axioms statementConditionalWitness_allFuel
#print axioms statementConditionalWitness_validated
#print axioms statementConditionalWitness_assignment
end Goose.Proofs.ConstructionAcceptedExecution

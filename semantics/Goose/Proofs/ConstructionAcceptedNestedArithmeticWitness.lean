import Goose.Proofs.ConstructionAcceptedNestedGlobalModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def nestedArithmeticEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩

private def nestedArithmeticConditional : Expr :=
  .ifE (.bool true)
    (.mk 0 [.assign (.global 0) (.lit .i64 7) 0] (some (.read (.global 0))))
    (.mk 1 [] (some (.lit .i64 4))) 0

private def nestedArithmeticExpression : Expr := .bin .add (.un .neg nestedArithmeticConditional 0) (.read (.global 0)) 0

private def nestedArithmeticModule : Module :=
  ⟨#["nested-arithmetic.goose"], #[.int .i64, .varr (.int .u8)],
    #[⟨"source", .int .i64, .mutable, .lit .i64 1, 0⟩,
      ⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [65] 0, 0⟩,
      ⟨"number", .int .i64, .immutable, nestedArithmeticExpression, 0⟩],
    #[nestedArithmeticEntry], #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 1, "assign"⟩], #[], #[]⟩

private def nestedArithmeticConfig : EvalConfig := ⟨.release, nestedArithmeticModule⟩

theorem nestedArithmetic_validated : validate nestedArithmeticModule = .ok () := by cbv

private def nestedArithmeticObservation : Option (Int × Int) :=
  match runModule 100 nestedArithmeticConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0), state.objects.lookup (.global 2) with
    | some (.int .i64 first), some (.int .i64 second) => some (first, second)
    | _, _ => none
  | _ => none

theorem nestedArithmetic_result : nestedArithmeticObservation = some (7, 0) := by decide +kernel

theorem nestedArithmetic_form : NestedScalarExpression nestedArithmeticExpression := by
  exact .binary .add 0
    (.unary .neg 0 (.conditional 0 (.scalar (.numeric (.scalar (.scalar (.boolean true)))))
      (.block 0 _ _ (.assign 0 (.lit .i64 7) 0 [] (.scalar (.numeric (.scalar (.scalar (.integer .i64 7))))) .nil)
        (.scalar (.numeric (.scalar (.scalar (.globalRead 0))))))
      (.block 1 [] _ .nil (.scalar (.numeric (.scalar (.scalar (.integer .i64 4))))))))
    (.scalar (.numeric (.scalar (.scalar (.globalRead 0)))))

theorem nestedArithmetic_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld nestedArithmeticConfig initialized
        (Goose.Proofs.Exit.stepState (runModule fuel nestedArithmeticConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel nestedArithmeticConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  have scalars : FlatGlobalsAreScalar nestedArithmeticConfig := by
    intro id descriptor declared flat
    cases id with
    | zero =>
      have same : descriptor = ⟨"source", .int .i64, .mutable, .lit .i64 1, 0⟩ := by
        simpa [nestedArithmeticConfig, nestedArithmeticModule] using declared.symm
      subst descriptor
      exact Or.inl ⟨.i64, rfl⟩
    | succ id =>
      cases id with
      | zero =>
        have same : descriptor = ⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [65] 0, 0⟩ := by
          simpa [nestedArithmeticConfig, nestedArithmeticModule] using declared.symm
        subst descriptor
        simp [Ty.flat] at flat
      | succ id =>
        cases id with
        | zero =>
          have same : descriptor = ⟨"number", .int .i64, .immutable, nestedArithmeticExpression, 0⟩ := by
            simpa [nestedArithmeticConfig, nestedArithmeticModule] using declared.symm
          subst descriptor
          exact Or.inl ⟨.i64, rfl⟩
        | succ id => simp [nestedArithmeticConfig, nestedArithmeticModule] at declared
  apply acceptedNestedGlobalModule_allFuel fuel nestedArithmeticConfig
    (acceptedModule nestedArithmeticConfig nestedArithmetic_validated) scalars ⟨0, "entry", [], [], []⟩ nestedArithmeticEntry
  · intro id inside
    change id < 3 at inside
    cases id with
    | zero => exact ⟨_, rfl, Or.inl ⟨.scalar (.numeric (.scalar (.scalar (.integer .i64 1)))), Or.inl ⟨.i64, rfl⟩⟩⟩
    | succ id =>
      cases id with
      | zero => exact ⟨_, rfl, Or.inr ⟨[65], 0, rfl, rfl⟩⟩
      | succ id =>
        cases id with
        | zero => exact ⟨_, rfl, Or.inl ⟨nestedArithmetic_form, Or.inl ⟨.i64, rfl⟩⟩⟩
        | succ id => omega
  · rfl
  · rfl
  · exact .nil
  · intro declaration member
    simp [nestedArithmeticEntry, Block.stmts] at member
  · intro id expression origin member
    simp [nestedArithmeticEntry, Block.stmts] at member
  · intro id expression origin member
    simp [nestedArithmeticEntry, Block.stmts] at member
  · intro id expression origin member
    simp [nestedArithmeticEntry, Block.stmts] at member
  · rfl

#print axioms nestedArithmetic_allFuel
#print axioms nestedArithmetic_form
#print axioms nestedArithmetic_validated
#print axioms nestedArithmetic_result

end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionAcceptedNestedGlobalModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def nestedBooleanEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩

private def nestedBooleanCondition : Expr :=
  .ifE (.bool true)
    (.mk 0 [.assign (.global 0) (.lit .i64 7) 0] (some (.read (.global 0))))
    (.mk 1 [] (some (.lit .i64 4))) 0

private def nestedBooleanSkipped : Expr :=
  .ifE (.bool true)
    (.mk 2 [.assign (.global 0) (.lit .i64 9) 0] (some (.bool false)))
    (.mk 3 [] (some (.bool false))) 0

private def nestedBooleanTaken : Expr :=
  .ifE (.cmp .eq (.read (.global 0)) (.lit .i64 7))
    (.mk 4 [.assign (.global 0) (.lit .i64 11) 0] (some (.bool true)))
    (.mk 5 [] (some (.bool false))) 0

private def nestedBooleanExpression : Expr :=
  .and (.or (.cmp .eq (.conv .widen (.int .i64) nestedBooleanCondition 0) (.lit .i64 7)) nestedBooleanSkipped)
    nestedBooleanTaken

private def nestedBooleanModule : Module :=
  ⟨#["nested-boolean.goose"], #[.int .i64, .varr (.int .u8)],
    #[⟨"source", .int .i64, .mutable, .lit .i64 1, 0⟩,
      ⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [65] 0, 0⟩,
      ⟨"number", .bool, .immutable, nestedBooleanExpression, 0⟩],
    #[nestedBooleanEntry], #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 1, "assign"⟩], #[], #[]⟩

private def nestedBooleanConfig : EvalConfig := ⟨.release, nestedBooleanModule⟩

theorem nestedBoolean_validated : validate nestedBooleanModule = .ok () := by cbv

private def nestedBooleanObservation : Option (Int × Bool) :=
  match runModule 100 nestedBooleanConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0), state.objects.lookup (.global 2) with
    | some (.int .i64 first), some (.bool second) => some (first, second)
    | _, _ => none
  | _ => none

theorem nestedBoolean_result : nestedBooleanObservation = some (11, true) := by decide +kernel

theorem nestedBoolean_form : NestedScalarExpression nestedBooleanExpression := by
  exact .conjunction
    (.disjunction
      (.comparison .eq
        (.conversion .widen (.int .i64) 0
          (.conditional 0 (.scalar (.numeric (.scalar (.scalar (.boolean true)))))
            (.block 0 _ _ (.assign 0 (.lit .i64 7) 0 [] (.scalar (.numeric (.scalar (.scalar (.integer .i64 7))))) .nil)
              (.scalar (.numeric (.scalar (.scalar (.globalRead 0))))))
            (.block 1 [] _ .nil (.scalar (.numeric (.scalar (.scalar (.integer .i64 4))))))))
        (.scalar (.numeric (.scalar (.scalar (.integer .i64 7))))))
      (.conditional 0 (.scalar (.numeric (.scalar (.scalar (.boolean true)))))
        (.block 2 _ _ (.assign 0 (.lit .i64 9) 0 [] (.scalar (.numeric (.scalar (.scalar (.integer .i64 9))))) .nil)
          (.scalar (.numeric (.scalar (.scalar (.boolean false))))))
        (.block 3 [] _ .nil (.scalar (.numeric (.scalar (.scalar (.boolean false))))))))
    (.conditional 0 (.comparison .eq (.scalar (.numeric (.scalar (.scalar (.globalRead 0)))))
        (.scalar (.numeric (.scalar (.scalar (.integer .i64 7))))))
      (.block 4 _ _ (.assign 0 (.lit .i64 11) 0 [] (.scalar (.numeric (.scalar (.scalar (.integer .i64 11))))) .nil)
        (.scalar (.numeric (.scalar (.scalar (.boolean true))))))
      (.block 5 [] _ .nil (.scalar (.numeric (.scalar (.scalar (.boolean false)))))))

theorem nestedBoolean_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld nestedBooleanConfig initialized
        (Goose.Proofs.Exit.stepState (runModule fuel nestedBooleanConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel nestedBooleanConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  have scalars : FlatGlobalsAreScalar nestedBooleanConfig := by
    intro id descriptor declared flat
    cases id with
    | zero =>
      have same : descriptor = ⟨"source", .int .i64, .mutable, .lit .i64 1, 0⟩ := by
        simpa [nestedBooleanConfig, nestedBooleanModule] using declared.symm
      subst descriptor
      exact Or.inl ⟨.i64, rfl⟩
    | succ id =>
      cases id with
      | zero =>
        have same : descriptor = ⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [65] 0, 0⟩ := by
          simpa [nestedBooleanConfig, nestedBooleanModule] using declared.symm
        subst descriptor
        simp [Ty.flat] at flat
      | succ id =>
        cases id with
        | zero =>
          have same : descriptor = ⟨"number", .bool, .immutable, nestedBooleanExpression, 0⟩ := by
            simpa [nestedBooleanConfig, nestedBooleanModule] using declared.symm
          subst descriptor
          exact Or.inr rfl
        | succ id => simp [nestedBooleanConfig, nestedBooleanModule] at declared
  apply acceptedNestedGlobalModule_allFuel fuel nestedBooleanConfig
    (acceptedModule nestedBooleanConfig nestedBoolean_validated) scalars ⟨0, "entry", [], [], []⟩ nestedBooleanEntry
  · intro id inside
    change id < 3 at inside
    cases id with
    | zero => exact ⟨_, rfl, Or.inl ⟨.scalar (.numeric (.scalar (.scalar (.integer .i64 1)))), Or.inl ⟨.i64, rfl⟩⟩⟩
    | succ id =>
      cases id with
      | zero => exact ⟨_, rfl, Or.inr ⟨[65], 0, rfl, rfl⟩⟩
      | succ id =>
        cases id with
        | zero => exact ⟨_, rfl, Or.inl ⟨nestedBoolean_form, Or.inr rfl⟩⟩
        | succ id => omega
  · rfl
  · rfl
  · exact .nil
  · intro declaration member
    simp [nestedBooleanEntry, Block.stmts] at member
  · intro id expression origin member
    simp [nestedBooleanEntry, Block.stmts] at member
  · intro id expression origin member
    simp [nestedBooleanEntry, Block.stmts] at member
  · intro id expression origin member
    simp [nestedBooleanEntry, Block.stmts] at member
  · rfl

#print axioms nestedBoolean_allFuel
#print axioms nestedBoolean_form
#print axioms nestedBoolean_validated
#print axioms nestedBoolean_result

end Goose.Proofs.ConstructionAcceptedExecution

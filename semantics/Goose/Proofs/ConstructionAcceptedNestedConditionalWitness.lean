import Goose.Proofs.ConstructionAcceptedAssignConditionalModule
import Goose.Proofs.ConstructionAcceptedNestedGlobalModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def nestedConditionalEntry : Impl :=
  ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩

private def nestedConditionalExpression : Expr :=
  .ifE (.bool true)
    (.mk 0 [] (some (.ifE (.bool true)
      (.mk 1 [.assign (.global 0) (.lit .i64 7) 0] (some (.read (.global 0))))
      (.mk 2 [] (some (.lit .i64 4))) 0)))
    (.mk 3 [] (some (.lit .i64 5))) 0

private def nestedConditionalModule : Module :=
  ⟨#["nested.goose"], #[.int .i64, .varr (.int .u8)],
    #[⟨"source", .int .i64, .mutable, .lit .i64 1, 0⟩,
      ⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [65] 0, 0⟩,
      ⟨"number", .int .i64, .immutable, nestedConditionalExpression, 0⟩],
    #[nestedConditionalEntry], #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 1, "assign"⟩], #[], #[]⟩

private def nestedConditionalConfig : EvalConfig := ⟨.release, nestedConditionalModule⟩

theorem nestedConditional_form : NestedScalarExpression nestedConditionalExpression := by
  exact .conditional 0 (.scalar (.numeric (.scalar (.scalar (.boolean true)))))
    (.block 0 [] _ .nil (.conditional 0 (.scalar (.numeric (.scalar (.scalar (.boolean true)))))
      (.block 1 _ _ (.assign 0 (.lit .i64 7) 0 [] (.scalar (.numeric (.scalar (.scalar (.integer .i64 7))))) .nil)
        (.scalar (.numeric (.scalar (.scalar (.globalRead 0))))))
      (.block 2 [] _ .nil (.scalar (.numeric (.scalar (.scalar (.integer .i64 4))))))))
    (.block 3 [] _ .nil (.scalar (.numeric (.scalar (.scalar (.integer .i64 5))))))

theorem nestedConditional_validated : validate nestedConditionalModule = .ok () := by cbv

private def nestedConditionalObservation : Option (Int × Int) :=
  match runModule 100 nestedConditionalConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0), state.objects.lookup (.global 2) with
    | some (.int .i64 first), some (.int .i64 second) => some (first, second)
    | _, _ => none
  | _ => none

theorem nestedConditional_result : nestedConditionalObservation = some (7, 7) := by decide +kernel

private def nestedConditionalTransition : Option (Int × Int) :=
  match initGlobals 100 nestedConditionalConfig [0] .initial with
  | .ok () before =>
    match before.objects.lookup (.global 0), evalValue 100 nestedConditionalConfig ⟨0, 1, #[], [], []⟩ nestedConditionalExpression before with
    | some (.int .i64 previous), .ok (.int .i64 _) after =>
      match after.objects.lookup (.global 0) with
      | some (.int .i64 current) => some (previous, current)
      | _ => none
    | _, _ => none
  | _ => none

theorem nestedConditional_changesEarlierGlobal : nestedConditionalTransition = some (1, 7) := by decide +kernel

theorem nestedConditional_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld nestedConditionalConfig initialized
        (Goose.Proofs.Exit.stepState (runModule fuel nestedConditionalConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel nestedConditionalConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  have scalars : FlatGlobalsAreScalar nestedConditionalConfig := by
    intro id descriptor declared flat
    cases id with
    | zero =>
      have same : descriptor = ⟨"source", .int .i64, .mutable, .lit .i64 1, 0⟩ := by
        simpa [nestedConditionalConfig, nestedConditionalModule] using declared.symm
      subst descriptor
      exact Or.inl ⟨.i64, rfl⟩
    | succ id =>
      cases id with
      | zero =>
        have same : descriptor = ⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [65] 0, 0⟩ := by
          simpa [nestedConditionalConfig, nestedConditionalModule] using declared.symm
        subst descriptor
        simp [Ty.flat] at flat
      | succ id =>
        cases id with
        | zero =>
          have same : descriptor = ⟨"number", .int .i64, .immutable, nestedConditionalExpression, 0⟩ := by
            simpa [nestedConditionalConfig, nestedConditionalModule] using declared.symm
          subst descriptor
          exact Or.inl ⟨.i64, rfl⟩
        | succ id => simp [nestedConditionalConfig, nestedConditionalModule] at declared
  apply acceptedNestedGlobalModule_allFuel fuel nestedConditionalConfig
    (acceptedModule nestedConditionalConfig nestedConditional_validated) scalars ⟨0, "entry", [], [], []⟩ nestedConditionalEntry
  · intro id inside
    change id < 3 at inside
    cases id with
    | zero => exact ⟨_, rfl, Or.inl ⟨.scalar (.numeric (.scalar (.scalar (.integer .i64 1)))), Or.inl ⟨.i64, rfl⟩⟩⟩
    | succ id =>
      cases id with
      | zero => exact ⟨_, rfl, Or.inr ⟨[65], 0, rfl, rfl⟩⟩
      | succ id =>
        cases id with
        | zero => exact ⟨_, rfl, Or.inl ⟨nestedConditional_form, Or.inl ⟨.i64, rfl⟩⟩⟩
        | succ id => omega
  · rfl
  · rfl
  · exact .nil
  · intro declaration member
    simp [nestedConditionalEntry, Block.stmts] at member
  · intro id expression origin member
    simp [nestedConditionalEntry, Block.stmts] at member
  · intro id expression origin member
    simp [nestedConditionalEntry, Block.stmts] at member
  · intro id expression origin member
    simp [nestedConditionalEntry, Block.stmts] at member
  · rfl

#print axioms nestedConditional_allFuel
#print axioms nestedConditional_form
#print axioms nestedConditional_validated
#print axioms nestedConditional_result
#print axioms nestedConditional_changesEarlierGlobal
end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionAcceptedNestedGlobalModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def nestedArithmeticEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩

private def nestedArithmeticConditional : Expr :=
  .ifE (.bool true)
    (.mk 0 [.assign (.global 0) (.lit .i64 7) 0] (some (.read (.global 0))))
    (.mk 1 [] (some (.lit .i64 4))) 0

private def nestedArithmeticExpression : Expr := .bin .add nestedArithmeticConditional (.lit .i64 1) 0

private def nestedArithmeticModule : Module :=
  ⟨#["nested-arithmetic.goose"], #[.int .i64],
    #[⟨"source", .int .i64, .mutable, .lit .i64 1, 0⟩,
      ⟨"number", .int .i64, .immutable, nestedArithmeticExpression, 0⟩],
    #[nestedArithmeticEntry], #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 1, "assign"⟩], #[], #[]⟩

private def nestedArithmeticConfig : EvalConfig := ⟨.release, nestedArithmeticModule⟩

theorem nestedArithmetic_validated : validate nestedArithmeticModule = .ok () := by cbv

private def nestedArithmeticObservation : Option (Int × Int) :=
  match runModule 100 nestedArithmeticConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0), state.objects.lookup (.global 1) with
    | some (.int .i64 first), some (.int .i64 second) => some (first, second)
    | _, _ => none
  | _ => none

theorem nestedArithmetic_result : nestedArithmeticObservation = some (7, 8) := by decide +kernel

theorem nestedArithmetic_notCovered : ¬ NestedScalarExpression nestedArithmeticExpression := by
  intro form
  cases form with
  | scalar form =>
    cases form with
    | numeric form => cases form <;> rename_i form <;> cases form <;> rename_i form <;> cases form
    | binary operation origin left right =>
      change AcceptedBinaryExpression (.ifE (.bool true)
        (.mk 0 [.assign (.global 0) (.lit .i64 7) 0] (some (.read (.global 0))))
        (.mk 1 [] (some (.lit .i64 4))) 0) at left
      cases left with
      | numeric form => cases form <;> rename_i form <;> cases form <;> rename_i form <;> cases form

#print axioms nestedArithmetic_validated
#print axioms nestedArithmetic_result
#print axioms nestedArithmetic_notCovered
end Goose.Proofs.ConstructionAcceptedExecution

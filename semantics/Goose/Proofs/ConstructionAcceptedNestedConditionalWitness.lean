import Goose.Proofs.ConstructionAcceptedAssignConditionalModule

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
  ⟨#["nested.goose"], #[.int .i64],
    #[⟨"source", .int .i64, .mutable, .lit .i64 1, 0⟩,
      ⟨"number", .int .i64, .immutable, nestedConditionalExpression, 0⟩],
    #[nestedConditionalEntry], #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 1, "assign"⟩], #[], #[]⟩

private def nestedConditionalConfig : EvalConfig := ⟨.release, nestedConditionalModule⟩

theorem nestedConditional_validated : validate nestedConditionalModule = .ok () := by cbv

private def nestedConditionalObservation : Option (Int × Int) :=
  match runModule 100 nestedConditionalConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0), state.objects.lookup (.global 1) with
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

#print axioms nestedConditional_validated
#print axioms nestedConditional_result
#print axioms nestedConditional_changesEarlierGlobal
end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionAcceptedConditionalTyping

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

private def conditionalConditionEntry : Impl :=
  ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩

private def conditionalConditionModule : Module :=
  ⟨#["condition.goose"], #[.bool, .int .i64],
    #[⟨"flag", .bool, .immutable, .bool true, 0⟩,
      ⟨"number", .int .i64, .immutable,
        .ifE (.not (.read (.global 0))) (.mk 0 [] (some (.lit .i64 3))) (.mk 1 [] (some (.lit .i64 4))) 0, 0⟩],
    #[conditionalConditionEntry], #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 1, "assign"⟩], #[], #[]⟩

private def conditionalConditionConfig : EvalConfig := ⟨.release, conditionalConditionModule⟩

theorem conditionalCondition_validated : validate conditionalConditionModule = .ok () := by cbv

private def conditionalConditionObservation : Option Int :=
  match initGlobals 100 conditionalConditionConfig [0, 1] .initial with
  | .ok () state => match state.objects.lookup (.global 1) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem conditionalCondition_initializer : conditionalConditionObservation = some 4 := by decide +kernel

theorem conditionalCondition_allFuel (fuel : Nat) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld conditionalConditionConfig 1 before ambient types live [] [])
    (clear : FutureGlobalsClear conditionalConditionConfig 1 before) :
    let activated := { before with nextAct := before.nextAct + 1 }
    let outcome := evalValue fuel conditionalConditionConfig ⟨0, before.nextAct, #[], [], []⟩
      (.not (.read (.global 0))) activated
    Goose.Proofs.Exit.stepState outcome = activated ∧
    AcceptedWorld conditionalConditionConfig 1 (Goose.Proofs.Exit.stepState outcome) ambient types live [] [] ∧
    (match outcome with | .ok (.bool _) _ | .stop _ _ => True | _ => False) := by
  exact accepted_globalConditional_condition_evaluates fuel conditionalConditionConfig
    (acceptedModule conditionalConditionConfig conditionalCondition_validated) 1 _ before ambient types live world clear rfl
    _ _ _ 0 rfl (.not (.numeric (.scalar (.scalar (.globalRead 0)))))

#print axioms conditionalCondition_allFuel
#print axioms conditionalCondition_validated
#print axioms conditionalCondition_initializer
end Goose.Proofs.ConstructionAcceptedExecution

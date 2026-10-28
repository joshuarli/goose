import Goose.Construct.Validate
import Goose.Construct.Eval

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

def scalarParameterWitness : Module :=
  ⟨#["mixed-helper.goose"], #[], #[],
    #[⟨"entry", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
        ⟨"number", .int .i64, .immutable, 0, 0⟩, ⟨"flag", .bool, .immutable, 0, 0⟩],
      .mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0,
        .letS 1 (.lit .i64 7) 0, .expr (.read (.var 1)) 0,
        .letS 2 (.bool true) 0, .expr (.not (.read (.var 2))) 0]
        (some (.call 1 [.byVal (.lit .i64 7)] 0)), .unknown⟩,
      ⟨"helper", #[⟨0, .byValue⟩], #[], #[⟨"parameter", .int .i64, .immutable, 0, 0⟩,
        ⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
        ⟨"number", .int .i64, .immutable, 0, 0⟩, ⟨"flag", .bool, .immutable, 0, 0⟩],
        .mk 0 [.letS 1 (.bytes (.varr (.int .u8)) [66, 67] 0) 0,
          .letS 2 (.read (.var 0)) 0, .expr (.read (.var 2)) 0,
          .letS 3 (.bool false) 0, .expr (.not (.read (.var 3))) 0] none, .unknown⟩],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [], []⟩], 0, #[⟨0, 1, "let"⟩], #[], #[]⟩

def scalarParameterWitnessAccepted : Bool :=
  match validate scalarParameterWitness with | .ok _ => true | .error _ => false

theorem scalarParameterWitness_validated : scalarParameterWitnessAccepted = true := by cbv

theorem scalarParameterWitness_validation : validate scalarParameterWitness = .ok () := by
  have accepted := scalarParameterWitness_validated
  unfold scalarParameterWitnessAccepted at accepted
  cases result : validate scalarParameterWitness with
  | error failure => simp [result] at accepted
  | ok value => cases value; rfl

def scalarParameterWitnessReturns : Bool :=
  match runModule 50 ⟨.release, scalarParameterWitness⟩ .initial with
  | .ok _ _ => true
  | _ => false

theorem scalarParameterWitness_returns : scalarParameterWitnessReturns = true := by cbv

#print axioms scalarParameterWitness_validation
#print axioms scalarParameterWitness_returns
end Goose.Proofs.ConstructionAcceptedExecution

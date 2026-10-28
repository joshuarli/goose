import Goose.Construct.Validate
import Goose.Construct.Eval

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

def scalarResultAssignmentsWitness : Module :=
  ⟨#["mixed-helper.goose"], #[], #[],
    #[⟨"entry", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
        ⟨"number", .int .i64, .immutable, 0, 0⟩, ⟨"flag", .bool, .immutable, 0, 0⟩,
        ⟨"result", .int .i64, .mutable, 0, 0⟩],
      .mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0,
        .letS 1 (.lit .i64 7) 0, .expr (.read (.var 1)) 0,
        .letS 2 (.bool true) 0, .expr (.not (.read (.var 2))) 0,
        .letS 3 (.call 1 [.byVal (.lit .i64 7)] 0) 0, .assign (.var 3) (.lit .i64 9) 0, .print [.expr (.read (.var 3))] 0] none, .unknown⟩,
      ⟨"helper", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩], #[⟨"parameter", .int .i64, .immutable, 0, 0⟩,
        ⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
        ⟨"number", .int .i64, .immutable, 0, 0⟩, ⟨"flag", .bool, .immutable, 0, 0⟩],
        .mk 0 [.letS 1 (.bytes (.varr (.int .u8)) [66, 67] 0) 0,
          .letS 2 (.read (.var 0)) 0, .expr (.read (.var 2)) 0,
          .letS 3 (.bool false) 0, .expr (.not (.read (.var 3))) 0] (some (.read (.var 0))), .unknown⟩],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [[]], []⟩], 0, #[⟨0, 1, "let"⟩], #[], #[]⟩

def scalarResultAssignmentsWitnessAccepted : Bool :=
  match validate scalarResultAssignmentsWitness with | .ok _ => true | .error _ => false

theorem scalarResultAssignmentsWitness_validated : scalarResultAssignmentsWitnessAccepted = true := by cbv

theorem scalarResultAssignmentsWitness_validation : validate scalarResultAssignmentsWitness = .ok () := by
  have accepted := scalarResultAssignmentsWitness_validated
  unfold scalarResultAssignmentsWitnessAccepted at accepted
  cases result : validate scalarResultAssignmentsWitness with
  | error failure => simp [result] at accepted
  | ok value => cases value; rfl

def scalarResultAssignmentsWitnessReturns : Bool :=
  match runModule 50 ⟨.release, scalarResultAssignmentsWitness⟩ .initial with
  | .ok _ after => after.construction.stdout == "9\n".toUTF8
  | _ => false

theorem scalarResultAssignmentsWitness_returns : scalarResultAssignmentsWitnessReturns = true := by cbv

#print axioms scalarResultAssignmentsWitness_validation
#print axioms scalarResultAssignmentsWitness_returns
end Goose.Proofs.ConstructionAcceptedExecution

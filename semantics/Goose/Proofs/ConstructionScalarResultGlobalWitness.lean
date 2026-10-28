import Goose.Construct.Validate
import Goose.Construct.Eval

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

def scalarResultGlobalWitness : Module :=
  ⟨#["mixed-helper.goose"], #[],
    #[⟨"counter", .int .i64, .mutable, .bin .add (.lit .i64 2) (.lit .i64 3) 0, 0⟩,
      ⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [71] 0, 0⟩],
    #[⟨"entry", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
        ⟨"number", .int .i64, .immutable, 0, 0⟩, ⟨"flag", .bool, .immutable, 0, 0⟩,
        ⟨"result", .int .i64, .immutable, 0, 0⟩],
      .mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0,
        .letS 1 (.lit .i64 7) 0, .expr (.read (.var 1)) 0,
        .letS 2 (.bool true) 0, .expr (.not (.read (.var 2))) 0,
        .letS 3 (.call 1 [.byVal (.lit .i64 7)] 0) 0, .assign (.global 0) (.lit .i64 9) 0, .print [.expr (.read (.var 3))] 0] none, .unknown⟩,
      ⟨"helper", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩], #[⟨"parameter", .int .i64, .immutable, 0, 0⟩,
        ⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
        ⟨"number", .int .i64, .immutable, 0, 0⟩, ⟨"flag", .bool, .immutable, 0, 0⟩],
        .mk 0 [.letS 1 (.bytes (.varr (.int .u8)) [66, 67] 0) 0,
          .letS 2 (.read (.var 0)) 0, .expr (.read (.var 2)) 0,
          .letS 3 (.bool false) 0, .expr (.not (.read (.var 3))) 0] (some (.read (.var 0))), .unknown⟩],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [[]], []⟩], 0, #[⟨0, 1, "let"⟩], #[], #[]⟩

def scalarResultGlobalWitnessAccepted : Bool :=
  match validate scalarResultGlobalWitness with | .ok _ => true | .error _ => false

theorem scalarResultGlobalWitness_validated : scalarResultGlobalWitnessAccepted = true := by cbv

theorem scalarResultGlobalWitness_validation : validate scalarResultGlobalWitness = .ok () := by
  have accepted := scalarResultGlobalWitness_validated
  unfold scalarResultGlobalWitnessAccepted at accepted
  cases result : validate scalarResultGlobalWitness with
  | error failure => simp [result] at accepted
  | ok value => cases value; rfl

def scalarResultGlobalWitnessReturns : Bool :=
  match runModule 50 ⟨.release, scalarResultGlobalWitness⟩ .initial with
  | .ok _ after => (after.construction.stdout == "7\n".toUTF8) &&
      (match after.objects.lookup (.global 0) with | some (.int .i64 value) => value == 9 | _ => false)
  | _ => false

theorem scalarResultGlobalWitness_returns : scalarResultGlobalWitnessReturns = true := by cbv

theorem scalarResultGlobalWitness_assignment :
    match runModule 50 ⟨.release, scalarResultGlobalWitness⟩ .initial with
    | .ok _ after => after.objects.lookup (.global 0) = some (.int .i64 9)
    | _ => False := by cbv

#print axioms scalarResultGlobalWitness_assignment
#print axioms scalarResultGlobalWitness_validation
#print axioms scalarResultGlobalWitness_returns
end Goose.Proofs.ConstructionAcceptedExecution

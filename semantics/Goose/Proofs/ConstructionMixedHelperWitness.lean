import Goose.Construct.Validate
import Goose.Construct.Eval

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

def mixedHelperWitness : Module :=
  ⟨#["mixed-helper.goose"], #[], #[],
    #[⟨"entry", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
        ⟨"number", .int .i64, .immutable, 0, 0⟩, ⟨"flag", .bool, .immutable, 0, 0⟩],
      .mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0,
        .letS 1 (.lit .i64 7) 0, .expr (.read (.var 1)) 0,
        .letS 2 (.bool true) 0, .expr (.not (.read (.var 2))) 0]
        (some (.call 1 [] 0)), .unknown⟩,
      ⟨"helper", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
        ⟨"number", .int .i64, .immutable, 0, 0⟩, ⟨"flag", .bool, .immutable, 0, 0⟩],
        .mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [66, 67] 0) 0,
          .letS 1 (.lit .i64 9) 0, .expr (.read (.var 1)) 0,
          .letS 2 (.bool false) 0, .expr (.not (.read (.var 2))) 0] none, .unknown⟩],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [], []⟩], 0, #[⟨0, 1, "let"⟩], #[], #[]⟩

def mixedHelperWitnessAccepted : Bool :=
  match validate mixedHelperWitness with | .ok _ => true | .error _ => false

theorem mixedHelperWitness_validated : mixedHelperWitnessAccepted = true := by cbv

theorem mixedHelperWitness_validation : validate mixedHelperWitness = .ok () := by
  have accepted := mixedHelperWitness_validated
  unfold mixedHelperWitnessAccepted at accepted
  cases result : validate mixedHelperWitness with
  | error failure => simp [result] at accepted
  | ok value => cases value; rfl

def mixedHelperWitnessReturns : Bool :=
  match runModule 50 ⟨.release, mixedHelperWitness⟩ .initial with
  | .ok _ _ => true
  | _ => false

theorem mixedHelperWitness_returns : mixedHelperWitnessReturns = true := by cbv

#print axioms mixedHelperWitness_validation
#print axioms mixedHelperWitness_returns
end Goose.Proofs.ConstructionAcceptedExecution

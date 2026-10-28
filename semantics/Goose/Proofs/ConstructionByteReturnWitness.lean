import Goose.Construct.Validate
import Goose.Construct.Eval

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

def byteReturnWitness : Module :=
  ⟨#["byte-return.goose"], #[], #[],
    #[⟨"entry", #[], #[], #[⟨"result", .varr (.int .u8), .immutable, 0, 0⟩],
      .mk 0 [.letS 0 (.call 1 [] 0) 0, .print [.view (.of (.var 0))] 0] none, .unknown⟩,
      ⟨"helper", #[], #[⟨.varr (.int .u8), .value, none⟩], #[],
        .mk 0 [] (some (.bytes (.varr (.int .u8)) [65, 66] 0)), .unknown⟩],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩

theorem byteReturnWitness_validation : validate byteReturnWitness = .ok () := by cbv

theorem byteReturnWitness_output :
    match eval 80 .release byteReturnWitness with
    | .done .returned stdout _ => stdout.data.toList = [65, 66, 10]
    | _ => False := by cbv

#print axioms byteReturnWitness_validation
#print axioms byteReturnWitness_output
end Goose.Proofs.ConstructionAcceptedExecution

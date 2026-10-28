import Goose.Construct.Validate
import Goose.Construct.Eval

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

def byteHelperTailWitness : Module :=
  ⟨#["unit-tail.goose"], #[], #[],
    #[⟨"entry", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩],
      .mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0]
        (some (.call 1 [] 0)), .unknown⟩,
      ⟨"helper", #[], #[], #[⟨"local", .varr (.int .u8), .immutable, 0, 0⟩],
        .mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [66, 67] 0) 0] none, .unknown⟩],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [], []⟩], 0, #[⟨0, 1, "let"⟩], #[], #[]⟩

def byteHelperTailWitnessAccepted : Bool :=
  match validate byteHelperTailWitness with | .ok _ => true | .error _ => false

theorem byteHelperTailWitness_validated : byteHelperTailWitnessAccepted = true := by cbv

theorem byteHelperTailWitness_validation : validate byteHelperTailWitness = .ok () := by
  have accepted := byteHelperTailWitness_validated
  unfold byteHelperTailWitnessAccepted at accepted
  cases result : validate byteHelperTailWitness with
  | error failure => simp [result] at accepted
  | ok value => cases value; rfl

def byteHelperTailWitnessReturns : Bool :=
  match runModule 30 ⟨.release, byteHelperTailWitness⟩ .initial with
  | .ok _ _ => true
  | _ => false

theorem byteHelperTailWitness_returns : byteHelperTailWitnessReturns = true := by cbv

#print axioms byteHelperTailWitness_validation
#print axioms byteHelperTailWitness_returns

end Goose.Proofs.ConstructionAcceptedExecution

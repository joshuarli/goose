import Goose.Construct.Validate
import Goose.Construct.Eval

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

def unitTailWitness : Module :=
  ⟨#["unit-tail.goose"], #[], #[],
    #[⟨"entry", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩],
      .mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0]
        (some (.call 1 [] 0)), .unknown⟩,
      ⟨"helper", #[], #[], #[], .mk 0 [] none, .unknown⟩],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [], []⟩], 0, #[⟨0, 1, "let"⟩], #[], #[]⟩

def unitTailWitnessAccepted : Bool :=
  match validate unitTailWitness with | .ok _ => true | .error _ => false

theorem unitTailWitness_validated : unitTailWitnessAccepted = true := by cbv

theorem unitTailWitness_validation : validate unitTailWitness = .ok () := by
  have accepted := unitTailWitness_validated
  unfold unitTailWitnessAccepted at accepted
  cases result : validate unitTailWitness with
  | error failure => simp [result] at accepted
  | ok value => cases value; rfl

def unitTailWitnessReturns : Bool :=
  match runModule 30 ⟨.release, unitTailWitness⟩ .initial with
  | .ok _ _ => true
  | _ => false

theorem unitTailWitness_returns : unitTailWitnessReturns = true := by cbv

#print axioms unitTailWitness_validation
#print axioms unitTailWitness_returns

end Goose.Proofs.ConstructionAcceptedExecution

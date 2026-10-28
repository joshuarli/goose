import Goose.Proofs.ConstructionAcceptedLiteralBlockValue

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem evalProduce_blockRegister (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (block : Block) (ty : Ty) (origin : Nat) :
    evalProduce (fuel + 1) config environment [.register ty] (.blockE block origin) =
      withBreakTarget environment.act .block [.register ty]
        (do let (flow, carriers) ← execResultBlock fuel config environment [.register ty] block
            match flow with
            | .normal _ => pure carriers
            | _ => fault .flow)
        (fun kind => do
          match kind with
          | .breakValue carriers => landCarriersInto origin [.register ty] carriers; pure carriers
          | .continueLoop => fault .flow) := by
  funext state
  simp only [evalProduce]
  rfl

#print axioms evalProduce_blockRegister
end Goose.Proofs.ConstructionAcceptedExecution

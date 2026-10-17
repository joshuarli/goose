import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntime
import Goose.Construct.Eval

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem enterActivation_no_jump (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (body : Block) (origin : Goose.Core.OriginId) (state : ExecutionState)
    (target : Nat) (kind : JumpKind) (after : ExecutionState) :
    enterActivation fuel config activation pre body origin state ≠ .jump target kind after := by
  cases fuel with
  | zero =>
      simp only [enterActivation, timeout, EvalM.stop]
      intro impossible; cases impossible
  | succ fuel =>
      simp only [enterActivation]
      cases implementation : config.module.impls[activation.implementation]? with
      | none =>
          intro impossible; cases impossible
      | some implementation =>
          exact finishActivation_no_jump _ _ _ _ _ _ _ _ _

#print axioms enterActivation_no_jump

end Goose.Proofs.ConstructionDelivery

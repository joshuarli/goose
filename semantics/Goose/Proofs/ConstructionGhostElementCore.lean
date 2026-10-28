import Goose.Construct.Eval

namespace Goose.Proofs.ConstructionGhostElements
open Goose.Construct

def fixedElementContinuation (fuel : Nat) (config : EvalConfig)
    (parent : Goose.Core.DestinationId) (element : Ty) (operand : Expr)
    (source : ExecutionStep Value) : ExecutionStep Unit :=
  match source with
  | .ok value state => (do
      let bytes ← liftExcept (fixedBytes fuel config.layout element value)
      receivingAction (expressionOrigin operand) parent (fun parent => writeElement parent bytes)) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem fixedElement_execution (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (parent : Goose.Core.DestinationId) (element : Ty) (operand : Expr) (before : ExecutionState)
    (fixed : element.nonfixed = false) :
    buildElement (fuel + 1) config environment parent element operand before =
      fixedElementContinuation fuel config parent element operand
        (evalValue fuel config environment operand before) := by
  simp only [buildElement, fixed, Bool.false_eq_true, ↓reduceIte, bind, fixedElementContinuation]
  cases evalValue fuel config environment operand before <;> rfl

#print axioms fixedElement_execution
end Goose.Proofs.ConstructionGhostElements

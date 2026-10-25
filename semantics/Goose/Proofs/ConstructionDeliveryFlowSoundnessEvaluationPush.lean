import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationProduceOperands

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem evaluationControl_push_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Option Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (.push owner expression origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (.push owner expression origin)) (fun _ => normalFlow)
      (pushValue (fuel + 1) config environment owner expression (origin.getD 0)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : placeQueryBudget owner + expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act
      (continueFlows (placeFlows staticFuel owner) (expressionFlows staticFuel expression)) (fun _ => normalFlow) _
    simp only [pushValue]
    apply controlFlow_bind
    · exact previous.place environment owner staticFuel (by omega)
    · intro location
      apply controlFlow_prefix
      · evaluation_values_normal
      · intro value
        cases value <;> try exact controlFlow_stop _ _ _
        rename_i stored
        apply controlFlow_prefix
        · evaluation_values_normal
        · intro pair
          rcases pair with ⟨destination, run⟩
          split
          · apply controlFlow_suffix
            · apply controlFlow_withOwnerExtension
              · evaluation_values_normal
              · intro destination
                apply controlFlow_suffix
                · exact previous.build environment destination expression staticFuel (by omega)
                · intro ignored
                  evaluation_values_normal
            · intro ignored
              evaluation_values_normal
          · apply controlFlow_suffix
            · exact previous.value environment expression staticFuel (by omega)
            · intro value
              evaluation_values_normal

#print axioms evaluationControl_push_succ

end Goose.Proofs.ConstructionDelivery

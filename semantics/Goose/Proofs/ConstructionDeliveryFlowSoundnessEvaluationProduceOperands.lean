import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationProduceHelpers

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem evaluationControl_operands_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (expressions : List Expr) (staticFuel : Nat)
    (enough : expressionListQueryBudget expressions ≤ staticFuel) :
    ControlFlowAction environment.act (expressionsFlows staticFuel expressions) (fun _ => normalFlow)
      (evalOperands (fuel + 1) config environment channels expressions) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionListQueryBudget_positive _) enough)
  | succ staticFuel =>
    cases channels with
    | nil =>
      cases expressions <;> simp only [evalOperands]
      · exact controlFlow_pure _ _ _ (List.mem_singleton_self _)
      · exact controlFlow_stop _ _ _
    | cons channel channels =>
      cases expressions with
      | nil => simp only [evalOperands]; exact controlFlow_stop _ _ _
      | cons expression rest =>
        have budgets : expressionQueryBudget expression + expressionListQueryBudget rest + 1 ≤ staticFuel + 1 := enough
        change ControlFlowAction environment.act
          (continueFlows (expressionFlows staticFuel expression) (expressionsFlows staticFuel rest)) (fun _ => normalFlow) _
        simp only [evalOperands]
        apply controlFlow_bind
        · exact previous.produce environment [channel] expression staticFuel (by omega)
        · intro carriers
          apply controlFlow_prefix
          · evaluation_produce_normal
          · intro carrier
            apply controlFlow_map
            exact previous.operands environment channels rest staticFuel (by omega)

theorem evaluationControl_element_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (parent : Goose.Core.DestinationId) (element : Ty) (operand : Expr) (staticFuel : Nat)
    (enough : expressionQueryBudget operand ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel operand) (fun _ => normalFlow)
      (buildElement (fuel + 1) config environment parent element operand) := by
  simp only [buildElement]
  split
  · apply controlFlow_prefix
    · evaluation_produce_normal
    · intro layout
      apply controlFlow_prefix
      · evaluation_produce_normal
      · intro child
        apply controlFlow_suffix
        · exact previous.build environment child operand staticFuel enough
        · intro ignored
          evaluation_produce_normal
  · apply controlFlow_suffix
    · exact previous.value environment operand staticFuel enough
    · intro value
      evaluation_produce_normal

#print axioms evaluationControl_operands_succ
#print axioms evaluationControl_element_succ

end Goose.Proofs.ConstructionDelivery

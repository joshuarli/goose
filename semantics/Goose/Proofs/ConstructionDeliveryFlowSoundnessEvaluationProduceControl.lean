import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationProduceHelpers

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem evaluationControl_resultBlockNormal (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (body : Block) (staticFuel : Nat)
    (enough : blockQueryBudget body ≤ staticFuel) (transform : List Carrier → α) :
    ControlFlowAction environment.act (blockFlows staticFuel body) (fun _ => normalFlow) (do
      let (flow, carriers) ← execResultBlock fuel config environment channels body
      match flow with
      | .normal _ => pure (transform carriers)
      | _ => fault .flow) := by
  apply controlFlow_dispatch (blockFlows staticFuel body) _
    (fun result : Flow × List Carrier => resultControlFlow result.1) (fun _ => normalFlow)
  · exact previous.resultBlock environment channels body staticFuel enough
  · intro scope kind present; exact present
  · intro result present
    rcases result with ⟨flow, carriers⟩
    cases flow with
    | normal value => exact controlFlow_pure _ _ _ present
    | breaking value => exact controlFlow_stop _ _ _
    | continuing => exact controlFlow_stop _ _ _

theorem evaluationControl_ifResultBlock (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (condition : Expr) (yes no : Block) (origin : Goose.Core.OriginId)
    (staticFuel : Nat) (enough : expressionQueryBudget (.ifE condition yes no origin) ≤ staticFuel)
    (transform : List Carrier → α) :
    ControlFlowAction environment.act (expressionFlows staticFuel (.ifE condition yes no origin)) (fun _ => normalFlow) (do
      let block := if (← expectBool (← evalValue fuel config environment condition)) then yes else no
      let (flow, carriers) ← execResultBlock fuel config environment channels block
      match flow with
      | .normal _ => pure (transform carriers)
      | _ => fault .flow) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget condition + blockQueryBudget yes + blockQueryBudget no + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act
      (continueFlows (expressionFlows staticFuel condition) (blockFlows staticFuel yes ++ blockFlows staticFuel no)) (fun _ => normalFlow) _
    apply controlFlow_bind
    · exact previous.value environment condition staticFuel (by omega)
    · intro value
      apply controlFlow_prefix
      · evaluation_produce_normal
      · intro boolean
        cases boolean with
        | true =>
          apply controlFlow_mono (blockFlows staticFuel yes)
          · intro flow present; exact List.mem_append_left _ present
          · exact evaluationControl_resultBlockNormal fuel config previous environment channels yes staticFuel (by omega) transform
        | false =>
          apply controlFlow_mono (blockFlows staticFuel no)
          · intro flow present; exact List.mem_append_right _ present
          · exact evaluationControl_resultBlockNormal fuel config previous environment channels no staticFuel (by omega) transform

theorem evaluationControl_producerBlock (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (body : Block) (origin : Goose.Core.OriginId)
    (staticFuel : Nat) (enough : expressionQueryBudget (.blockE body origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (.blockE body origin)) (fun _ => normalFlow)
      (withBreakTarget environment.act .block channels
        (do
          let (flow, carriers) ← execResultBlock fuel config environment channels body
          match flow with
          | .normal _ => pure carriers
          | _ => fault .flow)
        (fun kind => do
          match kind with
          | .breakValue carriers => landCarriersInto origin channels carriers; pure carriers
          | .continueLoop => fault .flow)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have bodyEnough : blockQueryBudget body ≤ staticFuel := by change blockQueryBudget body + 1 ≤ staticFuel + 1 at enough; omega
    apply controlFlow_withBreakTarget environment.act .block channels (blockFlows staticFuel body)
    · exact evaluationControl_resultBlockNormal fuel config previous environment channels body staticFuel bodyEnough id
    · intro value present
      apply List.mem_map.mpr
      exact ⟨normalFlow, present, rfl⟩
    · intro scope kind different present
      cases scope with
      | block => exact False.elim (different rfl)
      | loop =>
        apply List.mem_map.mpr
        refine ⟨jumpControlFlow .loop kind, present, ?_⟩
        cases kind <;> rfl
    · intro kind
      cases kind with
      | continueLoop => exact breakFrame_stop _
      | breakValue carriers =>
        apply breakFrame_bind
        · exact breakFrame_landCarriersInto _ _ _
        · intro ignored; exact breakFrame_pure _
    · intro kind present
      cases kind with
      | continueLoop => exact controlFlow_stop _ _ _
      | breakValue carriers =>
        apply controlFlow_prefix
        · exact controlFlow_landCarriersInto origin channels carriers
        · intro ignored
          apply controlFlow_pure
          apply List.mem_map.mpr
          exact ⟨valueBreakFlow, present, rfl⟩

theorem evaluationControl_buildBlock (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (body : Block) (origin : Goose.Core.OriginId)
    (staticFuel : Nat) (enough : expressionQueryBudget (.blockE body origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (.blockE body origin)) (fun _ => normalFlow)
      (withBreakTarget environment.act .block [.construct destination]
        (do
          let (flow, _) ← execResultBlock fuel config environment [.construct destination] body
          match flow with
          | .normal _ => pure ()
          | _ => fault .flow)
        (fun kind => do
          match kind with
          | .breakValue carriers => landCarriersInto origin [.construct destination] carriers
          | .continueLoop => fault .flow)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have bodyEnough : blockQueryBudget body ≤ staticFuel := by change blockQueryBudget body + 1 ≤ staticFuel + 1 at enough; omega
    apply controlFlow_withBreakTarget environment.act .block [.construct destination] (blockFlows staticFuel body)
    · exact evaluationControl_resultBlockNormal fuel config previous environment [.construct destination] body staticFuel bodyEnough (fun _ => ())
    · intro value present
      apply List.mem_map.mpr
      exact ⟨normalFlow, present, rfl⟩
    · intro scope kind different present
      cases scope with
      | block => exact False.elim (different rfl)
      | loop =>
        apply List.mem_map.mpr
        refine ⟨jumpControlFlow .loop kind, present, ?_⟩
        cases kind <;> rfl
    · intro kind
      cases kind with
      | continueLoop => exact breakFrame_stop _
      | breakValue carriers => exact breakFrame_landCarriersInto _ _ _
    · intro kind present
      cases kind with
      | continueLoop => exact controlFlow_stop _ _ _
      | breakValue carriers =>
        apply controlFlow_mono [normalFlow]
        · intro flow admitted
          have equal := List.mem_singleton.mp admitted
          subst flow
          apply List.mem_map.mpr
          exact ⟨valueBreakFlow, present, rfl⟩
        · exact controlFlow_landCarriersInto origin [.construct destination] carriers


#print axioms evaluationControl_resultBlockNormal
#print axioms evaluationControl_ifResultBlock
#print axioms evaluationControl_producerBlock
#print axioms evaluationControl_buildBlock

end Goose.Proofs.ConstructionDelivery

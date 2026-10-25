import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationProduceHelpers

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

private theorem produce_forIn_yield_cons (item : α) (rest : List α) (initial : β)
    (action : α → EvalM Unit) :
    (forIn (item :: rest) initial fun item current => do
      action item
      pure (ForInStep.yield current)) = (do
      action item
      forIn rest initial fun item current => do
        action item
        pure (ForInStep.yield current)) := by
  funext before
  simp only [List.forIn_cons, bind, Bind.bind]
  cases action item before <;> rfl

private theorem produce_forIn_yield_cons_after (item : α) (rest : List α) (initial : β)
    (evaluate : α → EvalM γ) (consume : γ → EvalM δ) :
    (forIn (item :: rest) initial fun item current => do
      let value ← evaluate item
      let _ ← consume value
      pure (ForInStep.yield current)) = (do
      let value ← evaluate item
      let _ ← consume value
      forIn rest initial fun item current => do
        let value ← evaluate item
        let _ ← consume value
        pure (ForInStep.yield current)) := by
  funext before
  simp only [List.forIn_cons, bind, Bind.bind]
  cases result : evaluate item before with
  | ok value middle =>
    dsimp only
    cases consume value middle <;> rfl
  | stop reason middle => rfl
  | escape target carriers middle => rfl
  | jump target kind middle => rfl

theorem evaluationControl_buildElements (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (element : Ty) (operands : List Expr)
    (staticFuel : Nat) (enough : expressionListQueryBudget operands ≤ staticFuel) (initial : α) :
    ControlFlowAction environment.act (expressionsFlows staticFuel operands) (fun _ => normalFlow)
      (forIn operands initial fun operand current => do
        buildElement fuel config environment destination element operand
        pure (ForInStep.yield current)) := by
  induction operands generalizing staticFuel initial with
  | nil =>
    cases staticFuel with
    | zero => exact False.elim (Nat.not_le_of_gt (expressionListQueryBudget_positive []) enough)
    | succ staticFuel => exact controlFlow_pure _ _ _ (List.mem_singleton_self _)
  | cons operand rest ih =>
    cases staticFuel with
    | zero => exact False.elim (Nat.not_le_of_gt (expressionListQueryBudget_positive _) enough)
    | succ staticFuel =>
      have budgets : expressionQueryBudget operand + expressionListQueryBudget rest + 1 ≤ staticFuel + 1 := enough
      rw [produce_forIn_yield_cons]
      change ControlFlowAction environment.act
        (continueFlows (expressionFlows staticFuel operand) (expressionsFlows staticFuel rest)) (fun _ => normalFlow) _
      apply controlFlow_bind
      · exact previous.element environment destination element operand staticFuel (by omega)
      · intro ignored
        exact ih staticFuel (by omega) initial

theorem evaluationControl_buildPrintArguments (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) (arguments : List PrintArg)
    (staticFuel : Nat) (enough : printArgumentsQueryBudget arguments ≤ staticFuel) (initial : α) :
    ControlFlowAction environment.act (printArgumentsFlows staticFuel arguments) (fun _ => normalFlow)
      (forIn arguments initial fun argument current => do
        let bytes ← evalPrintArg fuel config environment argument
        for byte in bytes.data do
          receivingAction origin destination (fun destination => writeElement destination ⟨#[byte]⟩)
        pure (ForInStep.yield current)) := by
  induction arguments generalizing staticFuel initial with
  | nil =>
    cases staticFuel with
    | zero => have positive := printArgumentsQueryBudget_positive []; omega
    | succ staticFuel => exact controlFlow_pure _ _ _ (List.mem_singleton_self _)
  | cons argument rest ih =>
    cases staticFuel with
    | zero => have positive := printArgumentsQueryBudget_positive (argument :: rest); omega
    | succ staticFuel =>
      have budgets : printArgumentQueryBudget argument + printArgumentsQueryBudget rest + 1 ≤ staticFuel + 1 := enough
      rw [produce_forIn_yield_cons_after]
      change ControlFlowAction environment.act
        (continueFlows (printArgumentFlows staticFuel argument) (printArgumentsFlows staticFuel rest)) (fun _ => normalFlow) _
      apply controlFlow_bind
      · exact previous.printArgument environment argument staticFuel (by omega)
      · intro bytes
        apply controlFlow_prefix
        · evaluation_produce_normal
        · intro ignored
          exact ih staticFuel (by omega) initial

#print axioms evaluationControl_buildElements
#print axioms evaluationControl_buildPrintArguments

end Goose.Proofs.ConstructionDelivery

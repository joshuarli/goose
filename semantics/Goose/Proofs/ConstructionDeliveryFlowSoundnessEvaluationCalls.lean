import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationProduceOperands
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationStatementsHelpers
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationFrames
import Goose.Proofs.ConstructionDeliveryFlowSoundnessCalls
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationStatementsReceive

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

private theorem controlFlow_materializeProducer_bind (fuel : Nat) (declarations : DeclarationEnv) (expression : Expr)
    (first second : List StaticFlow) (resultFlow : α → StaticFlow) (evaluate : EvalM Value)
    (next : Option (Array Value) → EvalM α)
    (body : ControlFlowAction activation first (fun _ => normalFlow) evaluate)
    (fallback : ControlFlowAction activation (continueFlows first second) resultFlow (next none))
    (materialized : ∀ values, ControlFlowAction activation second resultFlow (next (some values))) :
    ControlFlowAction activation (continueFlows first second) resultFlow (do
      let value ← materializeProducer fuel declarations expression evaluate
      next value) := by
  cases query : ordinaryProducerCount? fuel declarations expression with
  | none =>
    simp only [materializeProducer, query]
    exact fallback
  | some count =>
    simp only [materializeProducer, query]
    have reassociate : ∀ (action : EvalM Value) (f : Value → EvalM (Option (Array Value))),
        ((action >>= f) >>= next) = (action >>= fun value => f value >>= next) := by
      intro action f
      funext before
      cases result : action before <;> simp only [bind, Bind.bind, result]
    rw [reassociate]
    apply controlFlow_bind
    · exact body
    · intro value
      cases value with
      | fixed values => exact materialized values
      | int ty value | bool value | unit | ref location | stored value | slice location start count | record id fields =>
        exact controlFlow_stop _ _ _

theorem evaluationControl_arguments_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameters : List Param) (arguments : List Arg) (staticFuel : Nat)
    (enough : argumentsQueryBudget arguments ≤ staticFuel) :
    ControlFlowAction environment.act (argumentsFlows staticFuel arguments) (fun _ => normalFlow)
      (evalArguments (fuel + 1) config environment vars parameters arguments) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (argumentsQueryBudget_positive _) enough)
  | succ staticFuel =>
    cases parameters with
    | nil =>
      cases arguments <;> simp only [evalArguments]
      · exact controlFlow_pure _ _ _ (List.mem_singleton_self _)
      · exact controlFlow_stop _ _ _
    | cons parameter parameters =>
      cases arguments with
      | nil => simp only [evalArguments]; exact controlFlow_stop _ _ _
      | cons argument arguments =>
        have finish (value : Value) : ControlFlowAction environment.act (argumentsFlows staticFuel arguments)
            (fun _ => normalFlow) (do
              let values ← evalArguments fuel config environment vars parameters arguments
              pure (value :: values)) := by
          apply controlFlow_map
          exact previous.arguments environment vars parameters arguments staticFuel (by
            have budgets : argumentQueryBudget argument + argumentsQueryBudget arguments + 1 ≤ staticFuel + 1 := enough
            have positive := argumentQueryBudget_positive argument
            omega)
        cases argument with
        | byVal expression =>
          have budgets : expressionQueryBudget expression + 1 + argumentsQueryBudget arguments + 1 ≤ staticFuel + 1 := enough
          cases staticFuel with
          | zero => have positive := expressionQueryBudget_positive expression; omega
          | succ staticFuel =>
            change ControlFlowAction environment.act
              (continueFlows (expressionFlows staticFuel expression) (argumentsFlows (staticFuel + 1) arguments)) (fun _ => normalFlow) _
            simp only [evalArguments]
            apply controlFlow_bind
            · exact previous.value environment expression staticFuel (by omega)
            · exact finish
        | byRef mutability place =>
          have budgets : placeQueryBudget place + 1 + argumentsQueryBudget arguments + 1 ≤ staticFuel + 1 := enough
          cases staticFuel with
          | zero => have positive := placeQueryBudget_positive place; omega
          | succ staticFuel =>
            change ControlFlowAction environment.act
              (continueFlows (placeFlows staticFuel place) (argumentsFlows (staticFuel + 1) arguments)) (fun _ => normalFlow) _
            simp only [evalArguments]
            apply controlFlow_bind
            · exact previous.place environment place staticFuel (by omega)
            · intro location
              exact finish (.ref location)

        | construct expression =>
          have budgets : expressionQueryBudget expression + 1 + argumentsQueryBudget arguments + 1 ≤ staticFuel + 1 := enough
          cases staticFuel with
          | zero => have positive := expressionQueryBudget_positive expression; omega
          | succ staticFuel =>
            change ControlFlowAction environment.act
              (continueFlows (expressionFlows staticFuel expression) (argumentsFlows (staticFuel + 1) arguments)) (fun _ => normalFlow) _
            simp only [evalArguments]
            split
            · apply controlFlow_materializeProducer_bind
              · exact previous.value environment expression staticFuel (by omega)
              · apply controlFlow_bind
                · apply controlFlow_constructLocal
                  intro destination
                  exact previous.build environment destination expression staticFuel (by omega)
                · intro carrier
                  apply controlFlow_prefix
                  · evaluation_values_normal
                  · exact finish
              · intro source
                apply controlFlow_prefix
                · exact controlFlow_normal _ (breakFrame_materializedDestination _ _ _ _ _ _ _)
                    (neverJumps_materializedDestination _ _ _ _ _ _ _)
                · intro destination
                  apply controlFlow_prefix
                  · evaluation_values_normal
                  · intro ignored
                    apply controlFlow_prefix
                    · evaluation_values_normal
                    · intro carrier
                      apply controlFlow_prefix
                      · evaluation_values_normal
                      · exact finish
            · apply controlFlow_bind
              · exact controlFlow_stop _ _ _
              · exact finish

theorem evaluationControl_call_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : argumentsQueryBudget arguments ≤ staticFuel) :
    ControlFlowAction environment.act (argumentsFlows staticFuel arguments) (fun _ => normalFlow)
      (invokeCall (fuel + 1) config environment context arguments channels origin) := by
  simp only [invokeCall]
  apply controlFlow_prefix
  · evaluation_values_normal
  · intro pair
    rcases pair with ⟨id, implementation⟩
    split
    · exact controlFlow_stop _ _ _
    · apply controlFlow_prefix
      · apply controlFlow_listMapM_normal
        intro pair
        rcases pair with ⟨channel, descriptor⟩
        rcases descriptor with ⟨ty, request, named⟩
        cases request <;> cases channel <;> evaluation_values_normal
      · intro callable
        apply controlFlow_suffix
        · exact previous.arguments environment implementation.vars implementation.params.toList arguments staticFuel enough
        · intro values
          apply controlFlow_prefix
          · apply controlFlow_listMapM_normal
            intro channel
            cases channel <;> evaluation_values_normal
          · intro renewed
            apply controlFlow_prefix
            · evaluation_values_normal
            · intro snapshot
              split
              · exact controlFlow_stop _ _ _
              · apply controlFlow_prefix
                · evaluation_values_normal
                · intro act
                  apply controlFlow_normal
                  · apply breakFrame_allocateActivation
                    apply breakFrame_bind
                    · exact (evaluationBreakFrames fuel config).activation _ _ _ _
                    · intro carriers; exact breakFrame_deliverCarriers _ _ _ _ _
                  · apply neverJumps_bind
                    · exact neverJumps_get
                    · intro state
                      apply neverJumps_bind
                      · exact neverJumps_set _
                      · intro ignored
                        apply neverJumps_bind
                        · exact fun state target kind after => enterActivation_no_jump fuel config _ _ _ _ state target kind after
                        · intro carriers; exact neverJumps_deliverCarriers _ _ _ _ _


#print axioms evaluationControl_arguments_succ
#print axioms evaluationControl_call_succ

end Goose.Proofs.ConstructionDelivery

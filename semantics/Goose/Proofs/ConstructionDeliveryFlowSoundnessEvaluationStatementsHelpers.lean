import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationExitChannels
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationValuesConstruct
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationFramesProducers

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

private theorem evaluationBind_assoc (action : EvalM α) (next : α → EvalM β) (finish : β → EvalM γ) :
    ((action >>= next) >>= finish) = (action >>= fun value => next value >>= finish) := by
  funext before
  cases result : action before <;> simp only [bind, Bind.bind, result]

theorem controlFlow_materializeProducer_then (fuel : Nat) (declarations : DeclarationEnv) (expression : Expr)
    (allowed : List StaticFlow) (resultFlow : α → StaticFlow) (evaluate : EvalM Value)
    (next : Option (Array Value) → EvalM α)
    (body : ControlFlowAction activation allowed (fun _ => normalFlow) evaluate)
    (fallback : ControlFlowAction activation allowed resultFlow (next none))
    (materialized : ∀ values, ControlFlowAction activation [normalFlow] resultFlow (next (some values))) :
    ControlFlowAction activation allowed resultFlow (do
      let value ← materializeProducer fuel declarations expression evaluate
      next value) := by
  cases query : ordinaryProducerCount? fuel declarations expression with
  | none =>
      simp only [materializeProducer, query]
      exact fallback
  | some count =>
      simp only [materializeProducer, query]
      rw [evaluationBind_assoc]
      apply controlFlow_suffix
      · exact body
      · intro value
        cases value with
        | fixed values => exact materialized values
        | int ty value | bool value | unit | ref location | stored value | slice location start count | record id fields =>
          exact controlFlow_stop _ _ _

theorem neverJumps_materializedDestination (fuel : Nat) (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (origin : Goose.Core.OriginId) (count : Nat) (value : Value) :
    NeverJumps (materializedDestination fuel layout owner ty origin count value) := by
  unfold materializedDestination
  repeat' first
    | (solve | evaluation_values_noJump)
    | apply neverJumps_bind
    | evaluation_values_intro

theorem controlFlow_returned (allowed : List StaticFlow) (resultFlow : α → StaticFlow)
    (target : Goose.Core.ActId) (carriers : List Carrier) :
    ControlFlowAction activation allowed resultFlow (returned target carriers) :=
  ⟨breakFrame_returned target carriers, fun _ _ => True.intro⟩

theorem controlFlow_escaped (allowed : List StaticFlow) (resultFlow : α → StaticFlow)
    (target : ExitAddress) (carriers : List Carrier) :
    ControlFlowAction activation allowed resultFlow (escaped target carriers) :=
  ⟨breakFrame_escaped target carriers, fun _ _ => True.intro⟩

macro "evaluation_statements_normal" : tactic => `(tactic|
  repeat' first
    | (solve | evaluation_values_leaf)
    | exact controlFlow_pure [normalFlow] resultControlFlow _ (List.mem_singleton_self _)
    | exact controlFlow_stop [normalFlow] resultControlFlow _
    | (with_reducible apply controlFlow_prefix)
    | evaluation_values_zeta
    | evaluation_values_intro
    | split)

#print axioms controlFlow_materializeProducer_then
#print axioms neverJumps_materializedDestination
#print axioms controlFlow_returned
#print axioms controlFlow_escaped

end Goose.Proofs.ConstructionDelivery

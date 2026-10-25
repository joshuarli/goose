import Goose.Proofs.ConstructionDeliveryFlowSoundnessOutcomes

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

@[simp] theorem continueFlows_normal_left (flows : List StaticFlow) :
    continueFlows [normalFlow] flows = flows := by
  simp [continueFlows, continueFlow_transition, normalFlow, blockFlows, blockFlow_transition]

@[simp] theorem continueFlows_normal_right (flows : List StaticFlow) :
    continueFlows flows [normalFlow] = flows := by
  induction flows with
  | nil => rfl
  | cons flow rest ih =>
      cases flow <;>
        simp_all [continueFlows, continueFlow_transition, normalFlow, blockFlows, blockFlow_transition]

theorem controlFlow_prefix (allowed : List StaticFlow) (resultFlow : β → StaticFlow)
    (action : EvalM α) (next : α → EvalM β)
    (head : ControlFlowAction activation [normalFlow] (fun _ => normalFlow) action)
    (tail : ∀ value, ControlFlowAction activation allowed resultFlow (next value)) :
    ControlFlowAction activation allowed resultFlow (action >>= next) := by
  simpa only [continueFlows_normal_left] using
    controlFlow_bind [normalFlow] allowed resultFlow action next head tail

theorem controlFlow_suffix {resultFlow : β → StaticFlow} (allowed : List StaticFlow) (action : EvalM α) (next : α → EvalM β)
    (head : ControlFlowAction activation allowed (fun _ => normalFlow) action)
    (tail : ∀ value, ControlFlowAction activation [normalFlow] resultFlow (next value)) :
    ControlFlowAction activation allowed resultFlow (action >>= next) := by
  simpa only [continueFlows_normal_right] using
    controlFlow_bind allowed [normalFlow] resultFlow action next head tail

theorem controlFlow_conditional (condition : Prop) [Decidable condition]
    (allowed : List StaticFlow) (resultFlow : α → StaticFlow) (yes no : EvalM α)
    (left : ControlFlowAction activation allowed resultFlow yes)
    (right : ControlFlowAction activation allowed resultFlow no) :
    ControlFlowAction activation allowed resultFlow (if condition then yes else no) := by
  split <;> assumption

#print axioms continueFlows_normal_left
#print axioms continueFlows_normal_right
#print axioms controlFlow_prefix
#print axioms controlFlow_suffix
#print axioms controlFlow_conditional

end Goose.Proofs.ConstructionDelivery

import Goose.Proofs.ExitExecutionInvocationProducers
import Goose.Proofs.ExitExecutionActivationChannelsHelpers

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem producerFreshOfOk (action : EvalM α) (initial final : ExecutionState) (value : α)
    (normal : action initial = .ok value final) (fresh : FreshActivations initial)
    (preserved : PreservesFresh action) : FreshActivations final := by
  simpa only [normal, Goose.Proofs.Exit.stepState] using preserved initial fresh

private theorem producerChannelsOfOk (action : EvalM α) (initial final : ExecutionState) (value : α)
    (normal : action initial = .ok value final) (fresh : FreshActivations initial)
    (preserved : PreservesActivationChannels action) :
    ActivationChannelsProjection final = ActivationChannelsProjection initial := by
  simpa only [normal, ActivationChannelsOutcome] using preserved initial fresh

theorem ProducerReceivingPrefix.fresh {environment : RuntimeActivation} {incoming planned channels : List Channel}
    {expression : Expr} {initial prepared : ExecutionState}
    (receiving : ProducerReceivingPrefix environment incoming expression initial planned channels prepared)
    (fresh : FreshActivations initial) : FreshActivations prepared := by
  cases receiving with
  | actual renewedState prepared planned channels renewed selected =>
      have freshRenewed := producerFreshOfOk _ _ _ _ renewed fresh (by
        apply preservesFresh_listMapM
        intro channel
        cases channel
        all_goals first
          | exact preservesFresh_pure _
          | (apply preservesFresh_bind
             · exact preservesFresh_lift _ _
             · intro destination; exact preservesFresh_pure _))
      apply producerFreshOfOk _ _ _ _ selected freshRenewed
      cases expression
      all_goals first
        | exact preservesFresh_pure _
        | (apply preservesFresh_listMapM
           intro channel
           exact preservesFresh_selectCompletionChannel _ _ _)

theorem ProducerBodyChild.fresh {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {planned channels : List Channel} {expression : Expr} {initial ready : ExecutionState}
    {β : Type} {child : ExitInvocation β}
    (body : ProducerBodyChild fuel config environment planned channels expression initial child ready)
    (previous : EvaluationPreservesFresh fuel config) (fresh : FreshActivations initial) :
    FreshActivations ready := by
  cases body
  all_goals first | exact fresh | skip
  case resultLocalBuild | conditionalResult =>
    apply producerFreshOfOk _ _ _ _ (by assumption) fresh
    fresh_eval previous

theorem BuilderBodyChild.fresh {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {destination : Nat} {expression : Expr} {initial ready : ExecutionState}
    {β : Type} {child : ExitInvocation β}
    (body : BuilderBodyChild fuel config environment destination expression initial child ready)
    (previous : EvaluationPreservesFresh fuel config) (fresh : FreshActivations initial) :
    FreshActivations ready := by
  cases body
  all_goals first | exact fresh | skip
  case conditionalResult | array | fillBuild | stringArgument =>
    apply producerFreshOfOk _ _ _ _ (by assumption) fresh
    fresh_eval previous

theorem ProducerInvocationChild.fresh {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {child : ExitInvocation β} {initial ready : ExecutionState}
    (site : ProducerInvocationChild config caller initial child ready)
    (previous : ∀ fuel, EvaluationPreservesFresh fuel config) (fresh : FreshActivations initial) :
    FreshActivations ready := by
  cases site with
  | produce receiving body => exact body.fresh (previous _) (receiving.fresh fresh)
  | build renewed body => exact body.fresh (previous _) (producerFreshOfOk _ _ _ _ renewed fresh (preservesFresh_lift _ _))
  | elementBuild fuel environment parent element operand initial ready child dynamic opened =>
      apply producerFreshOfOk _ _ _ _ opened fresh
      have earlier := previous fuel
      fresh_eval earlier
  | elementValue => exact fresh

theorem ProducerReceivingPrefix.channels (config : EvalConfig)
    {environment : RuntimeActivation} {incoming planned channels : List Channel}
    {expression : Expr} {initial prepared : ExecutionState}
    (receiving : ProducerReceivingPrefix environment incoming expression initial planned channels prepared)
    (fresh : FreshActivations initial) :
    ActivationChannelsProjection prepared = ActivationChannelsProjection initial := by
  cases receiving with
  | actual renewedState prepared planned channels renewed selected =>
      have earlier := evaluation_preservesFresh 0 config
      have channelEarlier := evaluationActivationChannels_zero config
      have freshRenewed := producerFreshOfOk _ _ _ _ renewed fresh (by fresh_eval earlier)
      have renewalProjection := producerChannelsOfOk _ _ _ _ renewed fresh (by
        activation_channels_helper_eval earlier channelEarlier config)
      apply Eq.trans _ renewalProjection
      apply producerChannelsOfOk _ _ _ _ selected freshRenewed
      cases expression <;> activation_channels_helper_eval earlier channelEarlier config

theorem ProducerBodyChild.channels {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {planned channels : List Channel} {expression : Expr} {initial ready : ExecutionState}
    {β : Type} {child : ExitInvocation β}
    (body : ProducerBodyChild fuel config environment planned channels expression initial child ready)
    (previous : EvaluationPreservesFresh fuel config) (channelPrevious : EvaluationActivationChannels fuel config)
    (fresh : FreshActivations initial) :
    ActivationChannelsProjection ready = ActivationChannelsProjection initial := by
  cases body
  all_goals first | rfl | skip
  case resultLocalBuild | conditionalResult =>
    apply producerChannelsOfOk _ _ _ _ (by assumption) fresh
    activation_channels_helper_eval previous channelPrevious config

theorem BuilderBodyChild.channels {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {destination : Nat} {expression : Expr} {initial ready : ExecutionState}
    {β : Type} {child : ExitInvocation β}
    (body : BuilderBodyChild fuel config environment destination expression initial child ready)
    (previous : EvaluationPreservesFresh fuel config) (channelPrevious : EvaluationActivationChannels fuel config)
    (fresh : FreshActivations initial) :
    ActivationChannelsProjection ready = ActivationChannelsProjection initial := by
  cases body
  all_goals first | rfl | skip
  case conditionalResult | array | fillBuild | stringArgument =>
    apply producerChannelsOfOk _ _ _ _ (by assumption) fresh
    activation_channels_helper_eval previous channelPrevious config

theorem ProducerInvocationChild.channels {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {child : ExitInvocation β} {initial ready : ExecutionState}
    (site : ProducerInvocationChild config caller initial child ready)
    (previous : ∀ fuel, EvaluationPreservesFresh fuel config)
    (channelPrevious : ∀ fuel, EvaluationActivationChannels fuel config)
    (fresh : FreshActivations initial) :
    ActivationChannelsProjection ready = ActivationChannelsProjection initial := by
  cases site with
  | produce receiving body =>
      exact (body.channels (previous _) (channelPrevious _) (receiving.fresh fresh)).trans
        (receiving.channels config fresh)
  | build renewed body =>
      have freshRenewed := producerFreshOfOk _ _ _ _ renewed fresh (preservesFresh_lift _ _)
      exact (body.channels (previous _) (channelPrevious _) freshRenewed).trans
        (producerChannelsOfOk _ _ _ _ renewed fresh (preservesActivationChannels_liftConstruction _ _))
  | elementBuild fuel environment parent element operand initial ready child dynamic opened =>
      apply producerChannelsOfOk _ _ _ _ opened fresh
      have earlier := previous fuel
      have channelEarlier := channelPrevious fuel
      activation_channels_helper_eval earlier channelEarlier config
  | elementValue => rfl

#print axioms ProducerInvocationChild.fresh
#print axioms ProducerInvocationChild.channels

end Goose.Proofs.ExitExecution

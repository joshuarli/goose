import Goose.Proofs.ExitExecutionPathContext
import Goose.Proofs.ExitExecutionInvocationProducersEscapeSupport

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private def completionPlan (channels : List Channel) (origin : Goose.Core.OriginId) : EvalM (List (Channel × Option Nat)) :=
  channels.mapM fun channel => match channel with
  | .construct incoming => do
      let token ← liftConstruction origin (waitExitDestination incoming)
      pure (Channel.completion token, some token)
  | .register ty => pure (Channel.register ty, none)
  | .completion _ => fault .flow

private theorem completionPlan_neverEscapes (channels : List Channel) (origin : Goose.Core.OriginId) :
    ProducerNeverEscapes (completionPlan channels origin) := by
  unfold completionPlan
  producer_never_escapes_base

private def completionFinish (origin : Goose.Core.OriginId) (tokens : List Nat)
    (step : ExecutionStep (List Carrier)) : ExecutionStep (List Carrier) :=
  match step with
  | .ok carriers state => finishBorrowedExitChannels origin [] tokens false carriers (.ok carriers) state
  | .stop reason state => finishBorrowedExitChannels origin [] tokens false [] (.stop reason) state
  | .escape target carriers state => finishBorrowedExitChannels origin [] tokens true carriers (.escape target carriers) state
  | .jump target kind state => finishBorrowedExitChannels origin [] tokens true
      (match kind with | .breakValue carriers => carriers | .continueLoop => []) (.jump target kind) state

private theorem withCompletionChannels_decomposition (channels : List Channel) (origin : Goose.Core.OriginId)
    (action : List Channel → EvalM (List Carrier)) (initial : ExecutionState) :
    withCompletionChannels channels origin action initial =
      match completionPlan channels origin initial with
      | .ok planned prepared => completionFinish origin (planned.filterMap Prod.snd)
          ((do materializeOwnedCarriers origin (planned.filterMap Prod.snd) (← action (planned.map Prod.fst))) prepared)
      | .stop reason after => .stop reason after
      | .escape target carriers after => .escape target carriers after
      | .jump target kind after => .jump target kind after := by
  unfold withCompletionChannels
  change (match ((do
    let planned ← completionPlan channels origin
    pure (planned.map Prod.fst, planned.filterMap Prod.snd)) initial) with
    | .ok (planned, tokens) prepared => _
    | .stop reason after => ExecutionStep.stop reason after
    | .escape target carriers after => ExecutionStep.escape target carriers after
    | .jump target kind after => ExecutionStep.jump target kind after) = _
  cases setup : completionPlan channels origin initial with
  | stop reason after | escape target carriers after | jump target kind after => simp only [bind, setup]
  | ok planned prepared =>
      simp only [bind, setup, pure]
      cases evaluated : ((do materializeOwnedCarriers origin (planned.filterMap Prod.snd) (← action (planned.map Prod.fst))) prepared)
      all_goals simp only [bind] at evaluated
      all_goals rw [evaluated]
      all_goals simp only [completionFinish, finishBorrowedExitChannels, exitChannelCleanupBorrowed,
        Bool.false_eq_true, ↓reduceIte, List.reverse_nil, List.forIn_nil, bind, pure]
      all_goals try rfl

private theorem completionCleanup_neverEscapes (origin : Goose.Core.OriginId)
    (tokens : List Nat) (cancel : Bool) (carriers : List Carrier) :
    ProducerNeverEscapes (exitChannelCleanupBorrowed origin [] tokens cancel carriers) := by
  cases cancel <;> unfold exitChannelCleanupBorrowed
  all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.reverse_nil, List.forIn_nil]
  all_goals producer_never_escapes_base

private theorem completionMaterialize_neverEscapes (origin : Goose.Core.OriginId)
    (tokens : List Nat) (carriers : List Carrier) :
    ProducerNeverEscapes (materializeOwnedCarriers origin tokens carriers) := by
  unfold materializeOwnedCarriers
  producer_never_escapes_base

private theorem completionCleanup_escape_result (origin : Goose.Core.OriginId) (tokens : List Nat)
    (cancel : Bool) (values : List Carrier) (result : ExecutionState → ExecutionStep (List Carrier))
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : finishBorrowedExitChannels origin [] tokens cancel values result initial = .escape address carriers final) :
    ∃ after, exitChannelCleanupBorrowed origin [] tokens cancel values initial = .ok () after ∧
      result after = .escape address carriers final := by
  unfold finishBorrowedExitChannels at escaped
  cases cleaned : exitChannelCleanupBorrowed origin [] tokens cancel values initial with
  | ok ignored after =>
      cases ignored
      simp only [cleaned] at escaped
      exact ⟨after, rfl, escaped⟩
  | stop reason after | jump target kind after => simp only [cleaned] at escaped; cases escaped
  | escape target payload after =>
      exact False.elim (completionCleanup_neverEscapes origin tokens cancel values initial target payload after cleaned)

theorem completionInvocation_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (expression : Expr)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : withCompletionChannels channels (expressionOrigin expression)
      (fun prepared => evalProduce fuel config environment prepared expression) initial = .escape address carriers final) :
    ∃ planned prepared before,
      CompletionPreparation channels (expressionOrigin expression) initial planned prepared ∧
      evalProduce fuel config environment (planned.map Prod.fst) expression prepared = .escape address carriers before ∧
      exitChannelCleanupBorrowed (expressionOrigin expression) [] (planned.filterMap Prod.snd) true carriers before = .ok () final := by
  rw [withCompletionChannels_decomposition] at escaped
  cases setup : completionPlan channels (expressionOrigin expression) initial with
  | stop reason after | jump target kind after => simp only [setup] at escaped; cases escaped
  | escape target payload after =>
      exact False.elim (completionPlan_neverEscapes channels _ initial target payload after setup)
  | ok planned prepared =>
      simp only [setup] at escaped
      cases evaluated : evalProduce fuel config environment (planned.map Prod.fst) expression prepared with
      | stop reason after | jump target kind after =>
          simp only [bind, evaluated, completionFinish] at escaped
          obtain ⟨afterCleanup, cleaned, impossible⟩ := completionCleanup_escape_result _ _ _ _ _ _ _ _ _ escaped
          cases impossible
      | escape target payload before =>
          simp only [bind, evaluated, completionFinish] at escaped
          obtain ⟨afterCleanup, cleaned, emitted⟩ := completionCleanup_escape_result _ _ _ _ _ _ _ _ _ escaped
          cases emitted
          exact ⟨planned, prepared, before, setup, evaluated, cleaned⟩
      | ok raw afterOperands =>
          simp only [bind, evaluated] at escaped
          cases materialized : materializeOwnedCarriers (expressionOrigin expression) (planned.filterMap Prod.snd) raw afterOperands with
          | ok completed after | stop reason after | jump target kind after =>
              simp only [materialized, completionFinish] at escaped
              obtain ⟨afterCleanup, cleaned, impossible⟩ := completionCleanup_escape_result _ _ _ _ _ _ _ _ _ escaped
              cases impossible
          | escape target payload after =>
              exact False.elim (completionMaterialize_neverEscapes _ _ raw afterOperands target payload after materialized)

theorem withCompletionChannels_after_escape (channels : List Channel) (origin : Goose.Core.OriginId)
    (action : List Channel → EvalM (List Carrier)) (initial prepared before : ExecutionState)
    (planned : List (Channel × Option Nat)) (address : ExitAddress) (carriers : List Carrier)
    (setup : CompletionPreparation channels origin initial planned prepared)
    (escaped : action (planned.map Prod.fst) prepared = .escape address carriers before) :
    withCompletionChannels channels origin action initial =
      finishBorrowedExitChannels origin [] (planned.filterMap Prod.snd) true carriers (.escape address carriers) before := by
  rw [withCompletionChannels_decomposition]
  change completionPlan channels origin initial = .ok planned prepared at setup
  rw [setup]
  simp only [bind, escaped, completionFinish]

theorem withCompletionChannels_after_stop (channels : List Channel) (origin : Goose.Core.OriginId)
    (action : List Channel → EvalM (List Carrier)) (initial prepared before : ExecutionState)
    (planned : List (Channel × Option Nat)) (reason : Goose.Core.Stop)
    (setup : CompletionPreparation channels origin initial planned prepared)
    (stopped : action (planned.map Prod.fst) prepared = .stop reason before) :
    withCompletionChannels channels origin action initial =
      finishBorrowedExitChannels origin [] (planned.filterMap Prod.snd) false [] (.stop reason) before := by
  rw [withCompletionChannels_decomposition]
  change completionPlan channels origin initial = .ok planned prepared at setup
  rw [setup]
  simp only [bind, stopped, completionFinish]


#print axioms completionInvocation_escape_inv
#print axioms withCompletionChannels_decomposition
end Goose.Proofs.ExitExecution

import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationGuards

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

local elab "exit_cleanup_bind" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``NeverJumps do throwError "expected jump exclusion"
  let some action := target.getAppArgs.back? | throwError "expected action"
  unless action.getAppFn.isConstOf ``Bind.bind do
    throwError "expected bind action"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply neverJumps_bind))

local macro "exit_cleanup_noJump" : tactic => `(tactic|
  repeat' first
    | exact neverJumps_pure _
    | exact neverJumps_stop _
    | exact neverJumps_get
    | apply neverJumps_lift
    | apply neverJumps_listMapM
    | apply neverJumps_forIn
    | apply neverJumps_conditional
    | exit_cleanup_bind
    | evaluation_values_intro
    | split
    | dsimp only)

theorem controlFlow_withExitChannels (source target : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) (allowed : List StaticFlow)
    (action : List Channel → EvalM (List Carrier))
    (body : ∀ channels, ControlFlowAction activation allowed (fun _ => normalFlow) (action channels)) :
    ControlFlowAction activation allowed (fun _ => normalFlow)
      (withExitChannels source target operands origin action) := by
  refine ⟨breakFrame_withExitChannels source target operands origin action (fun channels => (body channels).frame), ?_⟩
  intro before bounded
  have preparedFrame := breakFrame_exitChannels source target operands origin before bounded
  cases prepared : exitChannels source target operands origin before with
  | stop reason after => simp only [withExitChannels, prepared, ControlFlowOutcome]
  | escape address carriers after => simp only [withExitChannels, prepared, ControlFlowOutcome]
  | jump id kind after => exact False.elim (neverJumps_exitChannels source target operands origin before id kind after prepared)
  | ok channels middle =>
    simp only [prepared] at preparedFrame
    change BreakStackFrame before middle at preparedFrame
    let tokens := (List.range (middle.construction.exitReservations.size - before.construction.exitReservations.size)).map
      (before.construction.exitReservations.size + ·)
    let evaluatedAction := do materializeOwnedCarriers origin tokens (← action channels)
    have actionControl : ControlFlowAction activation allowed (fun _ => normalFlow) evaluatedAction :=
      controlFlow_suffix allowed (action channels) _ (body channels)
        (fun carriers => controlFlow_normal _
          (breakFrame_materializeOwnedCarriers origin tokens carriers)
          (neverJumps_materializeOwnedCarriers origin tokens carriers))
    have outcome := actionControl.outcome middle (preparedFrame.bounded bounded)
    cases evaluated : evaluatedAction middle
    all_goals simp only [evaluated, ControlFlowOutcome] at outcome
    all_goals have evaluatedResult := evaluated
    all_goals dsimp only [evaluatedAction, tokens] at evaluatedResult
    all_goals simp only [withExitChannels, prepared, evaluatedResult]
    all_goals
      apply controlFlow_cleanup
      · intro final
        simpa only [ControlFlowOutcome, preparedFrame.stack] using outcome
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exit_cleanup_noJump

theorem controlFlow_withCompletionChannels (channels : List Channel) (origin : Goose.Core.OriginId)
    (allowed : List StaticFlow) (action : List Channel → EvalM (List Carrier))
    (body : ∀ planned, ControlFlowAction activation allowed (fun _ => normalFlow) (action planned)) :
    ControlFlowAction activation allowed (fun _ => normalFlow) (withCompletionChannels channels origin action) := by
  let setup : EvalM (List Channel × List ExitReservationId) := do
    let planned ← channels.mapM fun channel => match channel with
      | .construct incoming => do
          let token ← liftConstruction origin (waitExitDestination incoming)
          pure (Channel.completion token, some token)
      | .register ty => pure (Channel.register ty, none)
      | .completion _ => fault .flow
    pure (planned.map Prod.fst, planned.filterMap Prod.snd)
  have setupFrame : BreakFrameAction setup := by
    unfold setup
    repeat' first
      | evaluation_values_frame
      | apply breakFrame_bind
      | apply breakFrame_listMapM
      | evaluation_values_intro
      | split
      | dsimp only
  have setupNoJump : NeverJumps setup := by
    unfold setup
    exit_cleanup_noJump
  refine ⟨breakFrame_withCompletionChannels channels origin action (fun planned => (body planned).frame), ?_⟩
  intro before bounded
  unfold withCompletionChannels
  dsimp only
  split
  next planned tokens middle prepared =>
    have preparedRun : setup before = .ok (planned, tokens) middle := prepared
    have preparedFrame := setupFrame before bounded
    simp only [preparedRun] at preparedFrame
    change BreakStackFrame before middle at preparedFrame
    let evaluatedAction := do materializeOwnedCarriers origin tokens (← action planned)
    have actionControl : ControlFlowAction activation allowed (fun _ => normalFlow) evaluatedAction :=
      controlFlow_suffix allowed (action planned) _ (body planned)
        (fun carriers => controlFlow_normal _
          (breakFrame_materializeOwnedCarriers origin tokens carriers)
          (neverJumps_materializeOwnedCarriers origin tokens carriers))
    have outcome := actionControl.outcome middle (preparedFrame.bounded bounded)
    cases evaluated : evaluatedAction middle
    all_goals simp only [evaluated, ControlFlowOutcome] at outcome
    all_goals have evaluatedResult := evaluated
    all_goals dsimp only [evaluatedAction] at evaluatedResult
    all_goals simp only [evaluatedResult]
    all_goals
      apply controlFlow_cleanup
      · intro final
        simpa only [ControlFlowOutcome, preparedFrame.stack] using outcome
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exit_cleanup_noJump
  next reason middle prepared => trivial
  next address carriers middle prepared => trivial
  next id kind middle prepared =>
    exact False.elim (setupNoJump before id kind middle prepared)

#print axioms controlFlow_withExitChannels
#print axioms controlFlow_withCompletionChannels

end Goose.Proofs.ConstructionDelivery

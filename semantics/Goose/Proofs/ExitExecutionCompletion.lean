import Goose.Proofs.ExitExecutionBase

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem preservesFresh_materializeProducer (fuel : Nat) (declarations : DeclarationEnv)
    (expression : Expr) (evaluate : EvalM Value) (preserved : PreservesFresh evaluate) :
    PreservesFresh (materializeProducer fuel declarations expression evaluate) := by
  unfold materializeProducer
  split
  · exact preservesFresh_pure _
  · apply preservesFresh_bind
    · exact preserved
    · intro value
      cases value <;> first | exact preservesFresh_pure _ | exact preservesFresh_stop _

theorem preservesFresh_materializedDestination (fuel : Nat) (layout : LayoutEnv)
    (owner : Goose.Core.ActId) (ty : Ty) (origin : Goose.Core.OriginId)
    (count : Nat) (value : Value) :
    PreservesFresh (materializedDestination fuel layout owner ty origin count value) := by
  unfold materializedDestination
  apply preservesFresh_bind
  · exact preservesFresh_newDestination _ _ _ _ _ _ _
  · intro destination
    apply preservesFresh_bind
    · exact preservesFresh_copyValue _ _ _ _ _ _
    · intro ignored
      exact preservesFresh_completedReceivingDestination _

private theorem fresh_cleanupResult (cleanup : EvalM Unit) (resume : ExecutionState → ExecutionStep α)
    (frame : ∀ state, Goose.Proofs.Exit.stepState (resume state) = state)
    (preserved : PreservesFresh cleanup) (state : ExecutionState) (fresh : FreshActivations state) :
    FreshActivations (Goose.Proofs.Exit.stepState (match cleanup state with
      | .ok () after => resume after
      | .stop reason after => .stop reason after
      | .escape target carriers after => .escape target carriers after
      | .jump target kind after => .jump target kind after)) := by
  have checked := preserved state fresh
  cases evaluated : cleanup state with
  | ok ignored final =>
    cases ignored
    simp only [evaluated, Goose.Proofs.Exit.stepState] at checked
    change FreshActivations (Goose.Proofs.Exit.stepState (resume final))
    rw [frame]
    exact checked
  | stop reason final | escape target carriers final | jump target kind final =>
    simpa only [evaluated, Goose.Proofs.Exit.stepState] using checked

theorem preservesFresh_withCompletionChannels (channels : List Channel)
    (origin : Goose.Core.OriginId) (action : List Channel → EvalM (List Carrier))
    (preserved : ∀ planned, PreservesFresh (action planned)) :
    PreservesFresh (withCompletionChannels channels origin action) := by
  let setup : EvalM (List Channel × List ExitReservationId) := do
    let planned ← channels.mapM fun channel => match channel with
      | .construct incoming => do
          let token ← liftConstruction origin (waitExitDestination incoming)
          pure (Channel.completion token, some token)
      | .register ty => pure (Channel.register ty, none)
      | .completion _ => fault .flow
    pure (planned.map Prod.fst, planned.filterMap Prod.snd)
  have setupPreserved : PreservesFresh setup := by
    apply preservesFresh_bind
    · apply preservesFresh_listMapM
      intro channel
      cases channel <;> repeat' first
        | exact preservesFresh_pure _
        | exact preservesFresh_stop _
        | exact preservesFresh_lift _ _
        | apply preservesFresh_bind
        | intro
    · intro ignored
      exact preservesFresh_pure _
  intro state fresh
  change FreshActivations (Goose.Proofs.Exit.stepState (match setup state with
    | .ok (planned, tokens) prepared => _
    | .stop reason after => .stop reason after
    | .escape target carriers after => .escape target carriers after
    | .jump target kind after => .jump target kind after))
  have preparedFresh := setupPreserved state fresh
  cases prepared : setup state with
  | stop reason after | escape target carriers after | jump target kind after =>
    simpa only [prepared, Goose.Proofs.Exit.stepState] using preparedFresh
  | ok pair after =>
    rcases pair with ⟨planned, tokens⟩
    simp only [prepared, Goose.Proofs.Exit.stepState] at preparedFresh
    let evaluatedAction := do materializeOwnedCarriers origin tokens (← action planned)
    have actionPreserved : PreservesFresh evaluatedAction := by
      apply preservesFresh_bind
      · exact preserved planned
      · exact preservesFresh_materializeOwnedCarriers origin tokens
    have evaluatedFresh := actionPreserved after preparedFresh
    cases evaluated : evaluatedAction after
    all_goals simp only [evaluated, Goose.Proofs.Exit.stepState] at evaluatedFresh
    all_goals have evaluatedResult := evaluated
    all_goals dsimp only [evaluatedAction] at evaluatedResult
    all_goals simp only [evaluatedResult]
    all_goals
      apply fresh_cleanupResult
      · exact fun _ => rfl
      · simp only [Bool.false_eq_true, ↓reduceIte]
        apply preservesFresh_bind
        · apply preservesFresh_listForIn
          intro token accumulator
          repeat' first
            | exact preservesFresh_pure _
            | exact preservesFresh_lift _ _
            | apply preservesFresh_bind
            | intro
        · intro ignored
          exact preservesFresh_pure _
      · exact evaluatedFresh

#print axioms preservesFresh_withCompletionChannels

end Goose.Proofs.ExitExecution

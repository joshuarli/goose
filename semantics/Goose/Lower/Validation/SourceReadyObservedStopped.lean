import Goose.Lower.Validation.ReplacementContentFlowSourceReadyStopped
import Goose.Lower.Validation.SourceReadyObservations

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem value_ready_with_observations_of_live
    {module : GIR.Module} {func : Func} {state : State} {action : B ValueId} {env : LEnv} {before : LS}
    (stopped : SummaryPreservation.StoppedGraph action)
    (active : before.cur.isSome = true → ValueReadyAt state action env before ∧
      EmitsOnly (ReadyCallObservations module func state) before (action env before).2) :
    ValueReadyAt state action env before ∧
      EmitsOnly (ReadyCallObservations module func state) before (action env before).2 := by
  cases current : before.cur with
  | none =>
    exact ⟨.of_stopped stopped current, .of_blocks (stopped env before _ _ rfl current).2.1⟩
  | some block => exact active (by simp [current])

#print axioms value_ready_with_observations_of_live

end Goose.Lower.Validation.ReplacementContentFlowSource

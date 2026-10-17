import Goose.Lower.Validation.ReplacementContentFlowSourceReadyBuilder
import Goose.Lower.Validation.SummaryPreservationStoppedGraph

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem ValueReadyAt.of_stopped {state : State} {action : B ValueId} {env : LEnv} {before : LS}
    (stopped : SummaryPreservation.StoppedGraph action) (dead : before.cur = none) :
    ValueReadyAt state action env before := by
  have unchanged := stopped env before _ _ rfl dead
  exact ⟨.of_blocks unchanged.2.1, by intro live; simp [unchanged.1] at live⟩

theorem ValuesReadyAt.of_stopped {state : State} {action : B (List ValueId)} {env : LEnv} {before : LS}
    (stopped : SummaryPreservation.StoppedGraph action) (dead : before.cur = none) :
    ValuesReadyAt state action env before := by
  have unchanged := stopped env before _ _ rfl dead
  exact ⟨.of_blocks unchanged.2.1, by intro live; simp [unchanged.1] at live⟩

theorem ValueReadyAt.of_live {state : State} {action : B ValueId} {env : LEnv} {before : LS}
    (stopped : SummaryPreservation.StoppedGraph action)
    (active : before.cur.isSome = true → ValueReadyAt state action env before) :
    ValueReadyAt state action env before := by
  cases current : before.cur with
  | none => exact .of_stopped stopped current
  | some block => exact active (by simp [current])

#print axioms ValueReadyAt.of_stopped
#print axioms ValuesReadyAt.of_stopped
#print axioms ValueReadyAt.of_live

end Goose.Lower.Validation.ReplacementContentFlowSource

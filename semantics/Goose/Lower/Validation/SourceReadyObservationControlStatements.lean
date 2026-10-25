import Goose.Lower.Validation.SourceReadyObservationControlExpressions

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {func : Func} {state : State} {le : LEnv} {before : LS}

theorem observation_ifStatement_none (loop : Option LoopCtx) (condition : Expr) (yes : Core.Block) (origin : OriginId) :
    let tested := lowerExpr condition le before
    let split := fork tested.1 le tested.2
    let input := (setCur (some split.1.1) le split.2).2
    EmitsOnly (ReadyCallObservations module func state) before tested.2 →
    (tested.2.cur.isSome = true → EmitsOnly (ReadyCallObservations module func state) input
      (lowerBlock loop [] false yes le input).2) →
    EmitsOnly (ReadyCallObservations module func state) before
      (lowerStmt loop (.ifS condition yes none origin) le before).2 := by
  dsimp only
  intro conditionChild yesChild
  unfold lowerStmt
  apply observation_bind (le := le) conditionChild
  apply observation_whenLive
  intro block current
  apply observation_bind (le := le) (emitsOnly_fork _ (.term module func state) _ le _ _ _ rfl)
  apply observation_bind (le := le) (emitsOnly_setCur _ _ le _ _ _ rfl)
  apply observation_bind (le := le) (yesChild (by simp [current]))
  apply observation_bind (le := le)
  · exact observation_term _ le _ _ _ rfl
  exact emitsOnly_setCur _ _ le _ _ _ rfl

theorem observation_ifStatement_some (loop : Option LoopCtx) (condition : Expr) (yes no : Core.Block) (origin : OriginId) :
    let tested := lowerExpr condition le before
    let split := fork tested.1 le tested.2
    let yesInput := (setCur (some split.1.1) le split.2).2
    let yesResult := lowerBlock loop [] false yes le yesInput
    let noInput := (setCur (some split.1.2) le yesResult.2).2
    let noResult := lowerBlock loop [] false no le noInput
    EmitsOnly (ReadyCallObservations module func state) before tested.2 →
    (tested.2.cur.isSome = true → EmitsOnly (ReadyCallObservations module func state) yesInput yesResult.2) →
    (tested.2.cur.isSome = true → EmitsOnly (ReadyCallObservations module func state) noInput noResult.2) →
    EmitsOnly (ReadyCallObservations module func state) before
      (lowerStmt loop (.ifS condition yes (some no) origin) le before).2 := by
  dsimp only
  intro conditionChild yesChild noChild
  unfold lowerStmt
  apply observation_bind (le := le) conditionChild
  apply observation_whenLive
  intro block current
  have live : (lowerExpr condition le before).2.cur.isSome = true := by simp [current]
  apply observation_bind (le := le) (emitsOnly_fork _ (.term module func state) _ le _ _ _ rfl)
  apply observation_bind (le := le) (emitsOnly_setCur _ _ le _ _ _ rfl)
  apply observation_bind (le := le) (yesChild live)
  apply observation_bind (le := le) (EmitsOnly.of_blocks rfl)
  apply observation_bind (le := le) (emitsOnly_setCur _ _ le _ _ _ rfl)
  apply observation_bind (le := le) (noChild live)
  apply observation_bind (le := le) (EmitsOnly.of_blocks rfl)
  exact observation_joinArms _ _ le _ _ _ rfl

theorem observation_assert (loop : Option LoopCtx) (condition : Expr) (origin : OriginId)
    (child : EmitsOnly (ReadyCallObservations module func state) before (lowerExpr condition le before).2) :
    EmitsOnly (ReadyCallObservations module func state) before
      (lowerStmt loop (.assertS condition origin) le before).2 := by
  let tested := lowerExpr condition le before
  have tail : EmitsOnlyRun (ReadyCallObservations module func state) (whenLive () fun _ => do
      let (passed, failed) ← fork tested.1
      setCur (some failed)
      emitTerm (.abort .assert (some origin))
      setCur (some passed)) := by
    apply EmitsOnlyRun.whenLive
    intro block
    apply (emitsOnly_fork _ (.term module func state) tested.1).bind
    rintro ⟨passed, failed⟩
    exact (emitsOnly_setCur _ (some failed)).bind fun _ =>
      (observation_term (.abort .assert (some origin))).bind fun _ => emitsOnly_setCur _ (some passed)
  exact child.trans (tail le tested.2 _ _ rfl)

#print axioms observation_ifStatement_none
#print axioms observation_ifStatement_some
#print axioms observation_assert

end Goose.Lower.Validation.ReplacementContentFlowSource

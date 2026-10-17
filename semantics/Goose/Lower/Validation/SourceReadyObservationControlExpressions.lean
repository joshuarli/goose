import Goose.Lower.Validation.SourceReadyObservationBlocks

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {func : Func} {state : State} {le : LEnv} {before : LS}

theorem observation_shortCircuit (isAnd : Bool) (value : ValueId) (rhs : B ValueId)
    (child : before.cur.isSome = true →
      let split := scFork isAnd value le before
      let input := (setCur (some split.1.1) le split.2).2
      EmitsOnly (ReadyCallObservations module func state) input (rhs le input).2) :
    EmitsOnly (ReadyCallObservations module func state) before (shortCircuit isAnd value rhs le before).2 := by
  unfold shortCircuit
  apply observation_whenLive
  intro block current
  apply observation_bind (le := le) (emitsOnly_scFork _ (.term module func state) isAnd value le before _ _ rfl)
  apply observation_bind (le := le) (emitsOnly_setCur _ _ le _ _ _ rfl)
  apply observation_bind (le := le) (child (by simp [current]))
  apply observation_bind (le := le)
  · exact observation_term _ le _ _ _ rfl
  apply observation_bind (le := le) (emitsOnly_setCur _ _ le _ _ _ rfl)
  exact .of_blocks rfl

theorem observation_and (left right : Expr)
    (first : EmitsOnly (ReadyCallObservations module func state) before (lowerExpr left le before).2)
    (second :
      let lhs := lowerExpr left le before
      EmitsOnly (ReadyCallObservations module func state) lhs.2 (shortCircuit true lhs.1 (lowerExpr right) le lhs.2).2) :
    EmitsOnly (ReadyCallObservations module func state) before (lowerExpr (.and left right) le before).2 := by
  exact observation_bind first second

theorem observation_or (left right : Expr)
    (first : EmitsOnly (ReadyCallObservations module func state) before (lowerExpr left le before).2)
    (second :
      let lhs := lowerExpr left le before
      EmitsOnly (ReadyCallObservations module func state) lhs.2 (shortCircuit false lhs.1 (lowerExpr right) le lhs.2).2) :
    EmitsOnly (ReadyCallObservations module func state) before (lowerExpr (.or left right) le before).2 := by
  exact observation_bind first second

theorem observation_ifExpression (condition : Expr) (yes no : Core.Block) :
    let tested := lowerExpr condition le before
    let split := fork tested.1 le tested.2
    let yesInput := (setCur (some split.1.1) le split.2).2
    let yesResult := lowerBlock none [] true yes le yesInput
    let noInput := (setCur (some split.1.2) le yesResult.2).2
    let noResult := lowerBlock none [] true no le noInput
    EmitsOnly (ReadyCallObservations module func state) before tested.2 →
    (tested.2.cur.isSome = true → EmitsOnly (ReadyCallObservations module func state) yesInput yesResult.2) →
    (tested.2.cur.isSome = true → EmitsOnly (ReadyCallObservations module func state) noInput noResult.2) →
    EmitsOnly (ReadyCallObservations module func state) before (lowerExpr (.ifE condition yes no) le before).2 := by
  dsimp only
  intro conditionChild yesChild noChild
  unfold lowerExpr
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
  apply observation_bind (le := le) (emitsOnly_joinValue _ (.term module func state) _ _ _ _ le _ _ _ rfl)
  apply observation_bind (le := le) (EmitsOnly.of_blocks (by rw [recordValueRootRecipe_run]))
  exact .of_blocks rfl

#print axioms observation_shortCircuit
#print axioms observation_and
#print axioms observation_or
#print axioms observation_ifExpression

end Goose.Lower.Validation.ReplacementContentFlowSource

import Goose.Lower.Validation.SourceReadyObservationControlExpressions

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {func : Func} {state : State} {le : LEnv} {before : LS}

theorem observation_rangeBack (integer : IntTy) (counter : ValueId) (header : BlockId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (rangeBack integer counter header) := by
  unfold rangeBack
  apply EmitsOnlyRun.bind (EmitsOnlyRun.unchanged (by intros; rfl))
  intro live
  cases live with
  | false => exact .pure _ _
  | true =>
    exact (ReadyCallObservations.emitDefinition (.next integer counter) (by intros; intro same; cases same)).bind
      fun value => observation_term (.br header [value])

theorem observation_loopBody (condition : ValueId) (body : Nat → BlockId → B ValueId) (back : B Unit) :
    let split := fork condition le before
    let input := (setCur (some split.1.1) le split.2).2
    let result := body before.stack.length split.1.2 le input
    EmitsOnly (ReadyCallObservations module func state) input result.2 →
    EmitsOnly (ReadyCallObservations module func state) result.2 (back le result.2).2 →
    EmitsOnly (ReadyCallObservations module func state) before (loopBody condition body back le before).2 := by
  dsimp only
  intro child backChild
  unfold loopBody
  apply observation_bind (le := le) (EmitsOnly.of_blocks rfl)
  apply observation_bind (le := le) (emitsOnly_fork _ (.term module func state) condition le before _ _ rfl)
  apply observation_bind (le := le) (emitsOnly_setCur _ _ le _ _ _ rfl)
  apply observation_bind (le := le) child
  apply observation_bind (le := le) backChild
  exact emitsOnly_setCur _ _ le _ _ _ rfl

theorem observation_while (header : BlockId) (condition : B ValueId) (body : Nat → BlockId → B ValueId) :
    let tested := condition le before
    let split := fork tested.1 le tested.2
    let input := (setCur (some split.1.1) le split.2).2
    EmitsOnly (ReadyCallObservations module func state) before tested.2 →
    (tested.2.cur.isSome = true → EmitsOnly (ReadyCallObservations module func state) input
      (body tested.2.stack.length split.1.2 le input).2) →
    EmitsOnly (ReadyCallObservations module func state) before (lowerWhile header condition body le before).2 := by
  dsimp only
  intro conditionChild bodyChild
  unfold lowerWhile
  apply observation_bind (le := le) conditionChild
  apply observation_whenLive
  intro block current
  apply observation_loopBody
  · exact bodyChild (by simp [current])
  · exact observation_term (.br header []) le _ _ _ rfl

theorem observation_range (integer : IntTy) (counter bound : ValueId) (header : BlockId)
    (body : Nat → BlockId → B ValueId) :
    let compared := emitDef (.cmp .lt integer counter bound) le before
    let split := fork compared.1 le compared.2
    let input := (setCur (some split.1.1) le split.2).2
    EmitsOnly (ReadyCallObservations module func state) input (body compared.2.stack.length split.1.2 le input).2 →
    EmitsOnly (ReadyCallObservations module func state) before (lowerRange integer counter bound header body le before).2 := by
  dsimp only
  intro child
  unfold lowerRange
  apply observation_bind (le := le) (action := emitDef (.cmp .lt integer counter bound))
    (ReadyCallObservations.emitDefinition _ (by intros; intro same; cases same) le before _ _ rfl)
  apply observation_loopBody
  · exact child
  exact observation_rangeBack integer counter header le _ _ _ rfl

theorem observation_eachLen (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (eachLen regrow owner sampled) := by
  cases regrow with
  | false => exact .pure _ _
  | true => exact ReadyCallObservations.emitDefinition _ (by intros; intro same; cases same)

theorem observation_each (regrow : Bool) (owner : Option ValueId) (sampled : ValueId)
    (header : BlockId) (counter : ValueId) (body : Nat → BlockId → B ValueId) :
    let length := eachLen regrow owner sampled le before
    let compared := emitDef (.cmp .lt .i64 counter length.1) le length.2
    let split := fork compared.1 le compared.2
    let input := (setCur (some split.1.1) le split.2).2
    EmitsOnly (ReadyCallObservations module func state) input (body compared.2.stack.length split.1.2 le input).2 →
    EmitsOnly (ReadyCallObservations module func state) before (lowerEach regrow owner sampled header counter body le before).2 := by
  dsimp only
  intro child
  unfold lowerEach
  apply observation_bind (le := le) (action := eachLen regrow owner sampled)
    (observation_eachLen regrow owner sampled le before _ _ rfl)
  apply observation_bind (le := le) (action := emitDef (.cmp .lt .i64 counter _))
    (ReadyCallObservations.emitDefinition _ (by intros; intro same; cases same) le _ _ _ rfl)
  apply observation_loopBody
  · exact child
  exact observation_rangeBack .i64 counter header le _ _ _ rfl

#print axioms observation_rangeBack
#print axioms observation_loopBody
#print axioms observation_while
#print axioms observation_range
#print axioms observation_each

end Goose.Lower.Validation.ReplacementContentFlowSource

import Goose.Lower.Validation.SourceReadyObservationLoops

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {func : Func} {state : State} {le : LEnv} {before : LS}

theorem observation_whileStatement (loop : Option LoopCtx) (condition : Expr) (body : Core.Block) (origin : OriginId) :
    let allocated := newBlock [] le before
    let bridged := (emitTerm (.br allocated.1.1 []) le allocated.2).2
    let header := (setCur (some allocated.1.1) le bridged).2
    let tested := lowerExpr condition le header
    let split := fork tested.1 le tested.2
    let input := (setCur (some split.1.1) le split.2).2
    EmitsOnly (ReadyCallObservations module func state) header tested.2 →
    (tested.2.cur.isSome = true → EmitsOnly (ReadyCallObservations module func state) input
      (lowerBlock (some ⟨tested.2.stack.length, split.1.2, .jump allocated.1.1⟩) [] false body le input).2) →
    EmitsOnly (ReadyCallObservations module func state) before
      (lowerStmt loop (.while condition body origin) le before).2 := by
  dsimp only
  intro conditionChild bodyChild
  unfold lowerStmt
  apply observation_bind (le := le) (emitsOnly_newBlock _ [] le before _ _ rfl)
  apply observation_bind (le := le)
  · exact observation_term _ le _ _ _ rfl
  apply observation_bind (le := le) (emitsOnly_setCur _ _ le _ _ _ rfl)
  exact observation_while _ _ _ conditionChild bodyChild

theorem observation_rangeStatement (loop : Option LoopCtx) (loopVariable : VarId) (lo hi : Expr)
    (body : Core.Block) (origin : OriginId) :
    let first := lowerExpr lo le before
    let last := lowerExpr hi le first.2
    let integer := intTyOf first.1 le last.2
    let allocated := newBlock [.data (.int integer.1)] le integer.2
    let counter := allocated.1.2.headD 0
    let bridged := (emitTerm (.br allocated.1.1 [first.1]) le allocated.2).2
    let header := (setCur (some allocated.1.1) le bridged).2
    let compared := emitDef (.cmp .lt integer.1 counter last.1) le header
    let split := fork compared.1 le compared.2
    let input := (setCur (some split.1.1) le split.2).2
    EmitsOnly (ReadyCallObservations module func state) before first.2 →
    EmitsOnly (ReadyCallObservations module func state) first.2 last.2 →
    (last.2.cur.isSome = true → EmitsOnly (ReadyCallObservations module func state) input
      (lowerBlock (some ⟨compared.2.stack.length, split.1.2, .next allocated.1.1 integer.1 counter⟩)
        [(loopVariable, counter, origin)] false body le input).2) →
    EmitsOnly (ReadyCallObservations module func state) before
      (lowerStmt loop (.forRange loopVariable lo hi body origin) le before).2 := by
  dsimp only
  intro firstChild lastChild bodyChild
  unfold lowerStmt
  apply observation_bind (le := le) firstChild
  apply observation_bind (le := le) lastChild
  apply observation_whenLive
  intro block current
  apply observation_bind (le := le) (action := intTyOf _)
    (ReadyCallObservations.integerType _ le _ _ _ rfl)
  apply observation_bind (le := le) (emitsOnly_newBlock _ _ le _ _ _ rfl)
  apply observation_bind (le := le)
  · exact observation_term _ le _ _ _ rfl
  apply observation_bind (le := le) (emitsOnly_setCur _ _ le _ _ _ rfl)
  exact observation_range _ _ _ _ _ (bodyChild (by simp [current]))

#print axioms observation_whileStatement
#print axioms observation_rangeStatement

end Goose.Lower.Validation.ReplacementContentFlowSource

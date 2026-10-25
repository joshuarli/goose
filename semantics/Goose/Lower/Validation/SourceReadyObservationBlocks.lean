import Goose.Lower.Validation.SourceReadyObservationControlSteps

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {func : Func} {state : State} {le : LEnv} {before : LS}

theorem observation_inScope {property : Inst → Prop} (scope : ScopeId) (action : B α)
    (child : EmitsOnly property (pushScope scope le before).2
      (action le (pushScope scope le before).2).2) :
    EmitsOnly property before (inScope scope action le before).2 := by
  unfold inScope
  apply observation_bind (EmitsOnly.of_blocks rfl)
  apply observation_bind child
  apply observation_bind (EmitsOnly.of_blocks rfl)
  exact .of_blocks rfl

theorem observation_blockValue (want : Bool) (value : Option Expr)
    (child : ∀ expression, value = some expression →
      EmitsOnly (ReadyCallObservations module func state) before (lowerExpr expression le before).2) :
    EmitsOnly (ReadyCallObservations module func state) before (lowerBlockValue want value le before).2 := by
  cases value with
  | some expression => exact child expression rfl
  | none =>
    cases want with
    | false => exact .of_blocks rfl
    | true => exact ReadyCallObservations.emitDefinition .constUnit (by intros; intro same; cases same) le before _ _ rfl

theorem observation_block (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId))
    (want : Bool) (scope : ScopeId) (statements : List Stmt) (value : Option Expr)
    (statementChild :
      let entered := (emitEffect (.enter scope) le before).2
      let pushed := (pushScope scope le entered).2
      let initialized := (initSlots bindings le pushed).2
      EmitsOnly (ReadyCallObservations module func state) initialized (lowerStmts loop statements le initialized).2)
    (valueChild :
      let entered := (emitEffect (.enter scope) le before).2
      let pushed := (pushScope scope le entered).2
      let initialized := (initSlots bindings le pushed).2
      let stated := (lowerStmts loop statements le initialized).2
      EmitsOnly (ReadyCallObservations module func state) stated (lowerBlockValue want value le stated).2) :
    EmitsOnly (ReadyCallObservations module func state) before
      (lowerBlock loop bindings want (.mk scope statements value) le before).2 := by
  unfold lowerBlock
  apply observation_bind (action := emitEffect (.enter scope)) (observation_effect (.enter scope) le before _ _ rfl)
  apply observation_inScope
  apply observation_bind (action := initSlots bindings) (observation_initSlots bindings _ _ _ _ rfl)
  apply observation_bind statementChild
  apply observation_bind valueChild
  apply observation_bind (action := emitEffect (.leave scope)) (observation_effect (.leave scope) _ _ _ _ rfl)
  exact .of_blocks rfl

theorem observation_statements_nil (loop : Option LoopCtx) :
    EmitsOnly (ReadyCallObservations module func state) before (lowerStmts loop [] le before).2 :=
  .of_blocks rfl

theorem observation_statements_cons (loop : Option LoopCtx) (statement : Stmt) (rest : List Stmt)
    (head : before.cur.isSome = true → EmitsOnly (ReadyCallObservations module func state)
      before (lowerStmt loop statement le before).2)
    (tail : before.cur.isSome = true → EmitsOnly (ReadyCallObservations module func state)
      (lowerStmt loop statement le before).2
      (lowerStmts loop rest le (lowerStmt loop statement le before).2).2) :
    EmitsOnly (ReadyCallObservations module func state) before
      (lowerStmts loop (statement :: rest) le before).2 := by
  unfold lowerStmts
  simp only [bind_run, isLive_run]
  split
  · exact (head ‹_›).trans (tail ‹_›)
  · exact .of_blocks rfl

theorem observation_blockExpression (body : Core.Block)
    (child : EmitsOnly (ReadyCallObservations module func state) before (lowerBlock none [] true body le before).2) :
    EmitsOnly (ReadyCallObservations module func state) before (lowerExpr (.blockE body) le before).2 := child

#print axioms observation_inScope
#print axioms observation_blockValue
#print axioms observation_block
#print axioms observation_statements_cons
#print axioms observation_blockExpression

end Goose.Lower.Validation.ReplacementContentFlowSource

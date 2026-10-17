import Goose.Lower.Validation.ReplacementScopedOperandsRetained

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem rhsOperands_block (floor : Nat) (loop : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (want : Bool)
    (scope : ScopeId) (statements : List Stmt) (value : Option Expr)
    (preFresh : RhsPreFresh floor pre)
    (statementsChild : RhsOperandsRun floor (lowerStmts loop statements))
    (valueChild : RhsOperandsRun floor (lowerBlockValue want value)) :
    RhsOperandsRun floor (lowerBlock loop pre want (.mk scope statements value)) := by
  intro env before bound
  let entered := emitEffect (.enter scope) env before
  let pushed := {entered.2 with stack := scope :: entered.2.stack}
  let initialized := initSlots pre env pushed
  let ended := lowerStmts loop statements env initialized.2
  have enteredBound : floor ≤ entered.2.vals.size :=
    Nat.le_trans bound (advB_emitEffect _ env before entered.1 entered.2 rfl).vals
  have initializedBound : floor ≤ initialized.2.vals.size :=
    Nat.le_trans enteredBound (advB_initSlots pre env pushed initialized.1 initialized.2 rfl).vals
  have endedBound : floor ≤ ended.2.vals.size := Nat.le_trans initializedBound
    (advB_lowerStmts loop statements env initialized.2 ended.1 ended.2 rfl).vals
  simp only [lowerBlock]
  apply (RhsOperandsAt.emitEffect _ _ _ _ (by simp [Effect.uses])).bind
  apply RhsOperandsAt.inScope
  apply (RhsOperandsAt.initSlots _ _ _ _ preFresh).bind
  apply (statementsChild env initialized.2 initializedBound).bind
  apply (valueChild env ended.2 endedBound).bind
  exact (RhsOperandsAt.emitEffect _ _ _ _ (by simp [Effect.uses])).bind
    (RhsOperandsAt.pure _ _ _ _)

theorem rhsOperands_statementsCons (floor : Nat) (loop : Option LoopCtx)
    (statement : Stmt) (rest : List Stmt)
    (statementChild : RhsOperandsRun floor (lowerStmt loop statement))
    (restChild : RhsOperandsRun floor (lowerStmts loop rest)) :
    RhsOperandsRun floor (lowerStmts loop (statement :: rest)) := by
  intro env before bound
  simp only [lowerStmts]
  apply (RhsOperandsAt.isLive _ _ _).bind
  split
  · apply RhsOperandsAt.bindRun (statementChild env before bound)
    intro result middle run
    exact restChild env middle (Nat.le_trans bound (advB_lowerStmt loop statement env before result middle run).vals)
  · exact RhsOperandsAt.pure _ _ _ _

theorem rhsOperands_continue (floor : Nat) (loop : Option LoopCtx) (origin : OriginId)
    (loopFresh : RhsLoopFresh floor loop) :
    RhsOperandsRun floor (lowerStmt loop (.cont origin)) := by
  intro env before bound
  simp only [lowerStmt]
  cases loop with
  | none => exact RhsOperandsAt.pure _ _ _ _
  | some loop =>
    apply (RhsOperandsAt.leaveTo _ _ _ _).bindRun
    intro result middle run
    cases continuation : loop.cont with
    | jump header => exact RhsOperandsAt.emitTerm _ _ _ _ (by simp [Term.uses])
    | next header type counter =>
      have counterFresh : floor ≤ counter := by
        simpa only [RhsLoopFresh, continuation] using loopFresh
      have middleBound := Nat.le_trans bound (advB_leaveTo loop.depth env before result middle run).vals
      apply RhsOperandsAt.bindFresh middleBound
        (RhsOperandsAt.emitDef _ _ _ _ (by simp [Op.uses, counterFresh]))
        (advB_emitDef _) (freshValue_emitDef _)
      intro next after _ _ nextFresh
      exact RhsOperandsAt.emitTerm _ _ _ _ (by simpa only [Term.uses, List.mem_singleton] using
        fun live value equal => equal ▸ nextFresh live)

end Goose.Lower.Validation

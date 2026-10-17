import Goose.Lower.Validation.ReplacementScopedOperandsEffects

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem rhs_emitEffect_current (effect : Effect) (env : LEnv) (before : LS) :
    (emitEffect effect env before).2.cur = before.cur := by
  cases current : before.cur with
  | none => rw [emitEffect_none _ _ current]; exact current
  | some block => rw [emitEffect_run _ _ current]; exact current

theorem RhsOperandsAt.initSlots_live (floor : Nat) (env : LEnv) (before : LS)
    (pre : List (SlotId × ValueId × OriginId))
    (fresh : before.cur.isSome = true → RhsPreFresh floor pre) :
    RhsOperandsAt floor env before (Goose.Lower.initSlots pre) := by
  induction pre generalizing before with
  | nil => exact RhsOperandsAt.pure _ _ _ _
  | cons entry rest ih =>
    simp only [Goose.Lower.initSlots]
    apply (RhsOperandsAt.emitEffect floor env before (.slotInit entry.1 entry.2.1 (some entry.2.2)) ?_).bind
    · apply ih
      intro live item member
      have originalLive : before.cur.isSome = true := by
        simpa only [rhs_emitEffect_current] using live
      exact fresh originalLive item (by simp [member])
    · simpa only [Effect.uses, List.mem_singleton] using
        fun live value equal => equal ▸ fresh live entry (by simp)

theorem rhsOperands_block_live (floor : Nat) (loop : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (want : Bool)
    (scope : ScopeId) (statements : List Stmt) (value : Option Expr)
    (statementsChild : RhsOperandsRun floor (lowerStmts loop statements))
    (valueChild : RhsOperandsRun floor (lowerBlockValue want value))
    (env : LEnv) (before : LS) (bound : floor ≤ before.vals.size)
    (preFresh : before.cur.isSome = true → RhsPreFresh floor pre) :
    RhsOperandsAt floor env before (lowerBlock loop pre want (.mk scope statements value)) := by
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
  apply (RhsOperandsAt.initSlots_live floor env pushed pre ?_).bind
  · apply (statementsChild env initialized.2 initializedBound).bind
    apply (valueChild env ended.2 endedBound).bind
    exact (RhsOperandsAt.emitEffect _ _ _ _ (by simp [Effect.uses])).bind
      (RhsOperandsAt.pure _ _ _ _)
  · intro live
    apply preFresh
    simpa only [pushed, entered, rhs_emitEffect_current] using live

end Goose.Lower.Validation

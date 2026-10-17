import Goose.Lower.Validation.EmittedTypingCoercions
import Goose.Lower.Validation.OperandStatements
import Goose.Lower.Validation.EmittedTypingControlCheckpoints

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem emitted_checked_effectAfterTwo {le : LEnv} {initial before : LS}
    (first second : B ValueId) (effect : ValueId → ValueId → Effect)
    (builder : EmittedBuilder le initial (second le (first le before).2).2)
    (firstValue : ValueRun first) (secondValue : ValueRun second)
    (secondAdvance : AdvB second) (secondDead : DeadRun second)
    (references : ∀ x y operand, operand ∈ (effect x y).uses → operand = x ∨ operand = y) :
    EmittedBuilder le initial ((do
      let x ← first
      let y ← second
      emitEffect (effect x y)) le before).2 := by
  apply builder.emitEffect
  intro active operand member
  rcases references _ _ operand member with rfl | rfl
  · have firstLive := secondDead.live_before rfl active
    have firstBound := firstValue le before _ _ rfl firstLive
    exact Nat.lt_of_lt_of_le firstBound (secondAdvance le (first le before).2 _ _ rfl).vals
  · exact secondValue le (first le before).2 _ _ rfl active

theorem emitted_checked_lowerStmt_assign {le : LEnv} {initial before : LS}
    (loop : Option LoopCtx) (place : Place) (expr : Expr) (origin : OriginId)
    (builder : EmittedBuilder le initial (lowerExpr expr le (lowerPlace place le before).2).2) :
    EmittedBuilder le initial (lowerStmt loop (.assign place expr origin) le before).2 := by
  exact emitted_checked_effectAfterTwo (lowerPlace place) (lowerExpr expr) (fun x y => .store x y (some origin))
    builder (value_lowerPlace place) (value_lowerExpr expr) (advB_lowerExpr expr) (dead_lowerExpr expr)
    (by intro x y operand member; simpa [Effect.uses] using member)

theorem emitted_checked_lowerStmt_append {le : LEnv} {initial before : LS}
    (loop : Option LoopCtx) (place : Place) (view : View) (origin : OriginId)
    (builder : EmittedBuilder le initial (lowerView view le (lowerPlace place le before).2).2) :
    EmittedBuilder le initial (lowerStmt loop (.append place view origin) le before).2 := by
  exact emitted_checked_effectAfterTwo (lowerPlace place) (lowerView view) (fun x y => .append x y (some origin))
    builder (value_lowerPlace place) (value_lowerView view) (advB_lowerView view) (dead_lowerView view)
    (by intro x y operand member; simpa [Effect.uses] using member)

theorem emitted_checked_lowerStmt_popN {le : LEnv} {initial before : LS}
    (loop : Option LoopCtx) (place : Place) (expr : Expr) (origin : OriginId)
    (builder : EmittedBuilder le initial (lowerExpr expr le (lowerPlace place le before).2).2) :
    EmittedBuilder le initial (lowerStmt loop (.popN place expr origin) le before).2 := by
  exact emitted_checked_effectAfterTwo (lowerPlace place) (lowerExpr expr) (fun x y => .popN x y (some origin))
    builder (value_lowerPlace place) (value_lowerExpr expr) (advB_lowerExpr expr) (dead_lowerExpr expr)
    (by intro x y operand member; simpa [Effect.uses] using member)

theorem emitted_checked_lowerStmt_clear {le : LEnv} {initial before : LS}
    (loop : Option LoopCtx) (place : Place) (origin : OriginId)
    (builder : EmittedBuilder le initial (lowerPlace place le before).2) :
    EmittedBuilder le initial (lowerStmt loop (.clear place origin) le before).2 := by
  apply builder.emitEffect
  intro active operand member
  have same : operand = (lowerPlace place le before).1 := by simpa [Effect.uses] using member
  subst operand
  exact value_lowerPlace place le before _ _ rfl active

theorem emitted_checked_lowerStmt_let {le : LEnv} {initial before : LS}
    (loop : Option LoopCtx) (slot : SlotId) (expr : Expr) (origin : OriginId)
    (builder : EmittedBuilder le initial (lowerExpr expr le before).2) :
    EmittedBuilder le initial (lowerStmt loop (.letS slot expr origin) le before).2 := by
  have coerced := builder.coerceSlot slot (lowerExpr expr le before).1 origin
  apply coerced.emitEffect (.slotInit slot
    (coerceSlot slot (lowerExpr expr le before).1 origin le (lowerExpr expr le before).2).1 (some origin))
  intro active operand member
  have same : operand = (coerceSlot slot (lowerExpr expr le before).1 origin le (lowerExpr expr le before).2).1 := by
    simpa [Effect.uses] using member
  subst operand
  exact value_coerceSlot rfl (value_lowerExpr expr le before _ _ rfl) active

theorem emitted_checked_lowerStmt_exit {le : LEnv} {initial before : LS}
    (loop : Option LoopCtx) (expr : Expr) (origin : OriginId)
    (builder : EmittedBuilder le initial (lowerExpr expr le before).2) :
    EmittedBuilder le initial (lowerStmt loop (.exit expr origin) le before).2 := by
  apply builder.emitTerm
  intro active operand member
  have same : operand = (lowerExpr expr le before).1 := by simpa [Term.uses] using member
  subst operand
  exact value_lowerExpr expr le before _ _ rfl active

theorem emitted_checked_lowerStmt_return_none {le : LEnv} {initial before : LS}
    (loop : Option LoopCtx) (origin : OriginId) (builder : EmittedBuilder le initial before) :
    EmittedBuilder le initial (lowerStmt loop (.ret none origin) le before).2 := by
  apply (builder.leaveTo 0).emitTerm (.ret [] (some origin))
  intro active operand member
  simp [Term.uses] at member

theorem emitted_checked_lowerStmt_return_some {le : LEnv} {initial before : LS}
    (loop : Option LoopCtx) (expr : Expr) (origin : OriginId)
    (builder : EmittedBuilder le initial (lowerExpr expr le before).2) :
    EmittedBuilder le initial (lowerStmt loop (.ret (some expr) origin) le before).2 := by
  let child := lowerExpr expr le before
  let coerced := coerceResult child.1 origin le child.2
  let left := leaveTo 0 le coerced.2
  have coercedBuilder := builder.coerceResult child.1 origin
  have leftBuilder := coercedBuilder.leaveTo 0
  have finished := leftBuilder.emitTerm (.ret [coerced.1] (some origin)) (by
    intro active operand member
    have same : operand = coerced.1 := by simpa [Term.uses] using member
    subst operand
    have coercedLive := (dead_leaveTo 0).live_before (show leaveTo 0 le coerced.2 = left from rfl) active
    have bound := value_coerceResult (show coerceResult child.1 origin le child.2 = coerced from rfl)
      (value_lowerExpr expr le before _ _ rfl) coercedLive
    exact Nat.lt_of_lt_of_le bound (advB_leaveTo 0 le coerced.2 _ _ (show leaveTo 0 le coerced.2 = left from rfl)).vals)
  simpa only [lowerStmt, bind_run, pure_run, child, coerced, left] using finished

theorem emitted_checked_lowerStmt_rebind {le : LEnv} {initial before : LS}
    (loop : Option LoopCtx) (slot : SlotId) (expr : Expr) (origin : OriginId) (descriptor : GIR.Slot)
    (slotRow : le.slots[slot]? = some descriptor)
    (builder : EmittedBuilder le initial (lowerExpr expr le before).2) :
    EmittedBuilder le initial (lowerStmt loop (.rebind slot expr origin) le before).2 := by
  let child := lowerExpr expr le before
  let coerced := coerceSlot slot child.1 origin le child.2
  let addressed := emitDef (.slotAddr slot) le coerced.2
  have coercedBuilder := builder.coerceSlot slot child.1 origin
  have addressSuccess : ∃ type, (Op.slotAddr slot).resultTy (tyEnv le coerced.2) = .ok type := by
    simp only [Op.resultTy, tyEnv, slotRow]
    exact ⟨_, rfl⟩
  have addressedBuilder := coercedBuilder.emitDef (.slotAddr slot)
    (fun _ => addressSuccess) (by intro active operand member; simp [Op.uses] at member)
  have finished := addressedBuilder.emitEffect (.store addressed.1 coerced.1 (some origin)) (by
    intro active operand member
    have either : operand = addressed.1 ∨ operand = coerced.1 := by simpa [Effect.uses] using member
    rcases either with rfl | rfl
    · exact value_emitDef (.slotAddr slot) le coerced.2 _ _ rfl active
    · have coercedLive := (dead_emitDef (.slotAddr slot)).live_before rfl active
      have bound := value_coerceSlot (show coerceSlot slot child.1 origin le child.2 = coerced from rfl)
        (value_lowerExpr expr le before _ _ rfl) coercedLive
      exact Nat.lt_of_lt_of_le bound (advB_emitDef (.slotAddr slot) le coerced.2 _ _ rfl).vals)
  simpa only [lowerStmt, bind_run, child, coerced, addressed] using finished

end Goose.Lower.Validation

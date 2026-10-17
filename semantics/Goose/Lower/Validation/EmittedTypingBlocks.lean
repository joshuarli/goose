import Goose.Lower.Validation.EmittedTypingLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem EmittedBuilder.initSlots {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (slots : List (SlotId × ValueId × OriginId))
    (bounded : ∀ slot value origin, (slot, value, origin) ∈ slots → value < before.vals.size) :
    EmittedBuilder le initial (Goose.Lower.initSlots slots le before).2 := by
  induction slots generalizing before with
  | nil => exact builder
  | cons entry rest inductionHypothesis =>
    rcases entry with ⟨slot, value, origin⟩
    have initialized := builder.emitEffect (.slotInit slot value (some origin)) (by
      intro active operand member
      have same : operand = value := by simpa [Effect.uses] using member
      subst operand
      exact bounded slot value origin (by simp))
    apply inductionHypothesis initialized
    intro nextSlot nextValue nextOrigin member
    have bound := bounded nextSlot nextValue nextOrigin (by simp [member])
    exact Nat.lt_of_lt_of_le bound (advB_emitEffect (.slotInit slot value (some origin)) le before _ _ rfl).vals

theorem emitted_checked_lowerBlock {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (loop : Option LoopCtx)
    (loopTypes : EmittedLoopTypes loop before) (pre : List (SlotId × ValueId × OriginId))
    (preBounds : ∀ slot value origin, (slot, value, origin) ∈ pre → value < before.vals.size)
    (want : Bool) (scope : ScopeId) (stmts : List Stmt) (value : Option Expr)
    (stmtsChecked : ∀ initial before, EmittedBuilder le initial before → EmittedLoopTypes loop before →
      EmittedBuilder le initial (Goose.Lower.lowerStmts loop stmts le before).2)
    (valueChecked : ∀ initial before, EmittedBuilder le initial before →
      EmittedBuilder le initial (Goose.Lower.lowerBlockValue want value le before).2) :
    EmittedBuilder le initial (Goose.Lower.lowerBlock loop pre want (.mk scope stmts value) le before).2 := by
  let entered := Goose.Lower.emitEffect (.enter scope) le before
  let pushed := Goose.Lower.pushScope scope le entered.2
  let initialized := Goose.Lower.initSlots pre le pushed.2
  let statements := Goose.Lower.lowerStmts loop stmts le initialized.2
  let output := Goose.Lower.lowerBlockValue want value le statements.2
  let left := Goose.Lower.emitEffect (.leave scope) le output.2
  have enteredBuilder := builder.emitEffect (.enter scope)
    (by intro active operand member; simp [Effect.uses] at member)
  have pushedBuilder := enteredBuilder.pushScope scope
  have initialPrefix := (EmittedAt.emitEffect le before (.enter scope)).prefix.trans
    (EmittedAt.pushScope le entered.2 scope).prefix
  have initializedBuilder := pushedBuilder.initSlots pre (by
    intro slot value origin member
    exact Nat.lt_of_lt_of_le (preBounds slot value origin member) initialPrefix.size)
  have initializedTypes := initialPrefix.typed.trans ((EmittedRun.initSlots pre le pushed.2).prefix.typed)
  have statementsBuilder := stmtsChecked initial initialized.2 initializedBuilder
    (loopTypes.retained initializedTypes)
  have outputBuilder := valueChecked initial statements.2 statementsBuilder
  have leftBuilder := outputBuilder.emitEffect (.leave scope)
    (by intro active operand member; simp [Effect.uses] at member)
  have poppedBuilder := leftBuilder.popScope
  simpa only [Goose.Lower.lowerBlock, Goose.Lower.inScope, bind_run, pure_run,
    entered, pushed, initialized, statements, output, left] using poppedBuilder


theorem emitted_checked_lowerBlockValue {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (want : Bool) (value : Option Expr)
    (childChecked : ∀ expr, value = some expr → ∀ initial before,
      EmittedBuilder le initial before → EmittedBuilder le initial (Goose.Lower.lowerExpr expr le before).2) :
    EmittedBuilder le initial (Goose.Lower.lowerBlockValue want value le before).2 := by
  cases value with
  | some expr => exact childChecked expr rfl initial before builder
  | none =>
    cases want
    · exact builder
    · exact builder.emitDef .constUnit (fun _ => ⟨.data .unit, rfl⟩)
        (by intro active value member; simp [Op.uses] at member)

theorem emitted_checked_lowerStmts {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (loop : Option LoopCtx)
    (loopTypes : EmittedLoopTypes loop before) (stmts : List Stmt)
    (stmtChecked : ∀ stmt ∈ stmts, ∀ initial before,
      EmittedBuilder le initial before → EmittedLoopTypes loop before → before.cur.isSome = true →
      EmittedBuilder le initial (Goose.Lower.lowerStmt loop stmt le before).2) :
    EmittedBuilder le initial (Goose.Lower.lowerStmts loop stmts le before).2 := by
  induction stmts generalizing before with
  | nil => exact builder
  | cons stmt rest inductionHypothesis =>
    cases live : before.cur with
    | none =>
      have active : Goose.Lower.isLive le before = (false, before) := isLive_none live
      simpa only [Goose.Lower.lowerStmts, bind_run, active, Bool.false_eq_true, reduceIte, pure_run] using builder
    | some block =>
      have active : Goose.Lower.isLive le before = (true, before) := by
        simp [Goose.Lower.isLive, Goose.Lower.curBlock, bind_run, live, pure_run]
      have stmtBuilder := stmtChecked stmt (by simp) initial before builder loopTypes (by rw [live]; rfl)
      have nextTypes := loopTypes.retained (types_lowerStmt loop stmt le before _ _ rfl)
      have nextBuilder := inductionHypothesis stmtBuilder nextTypes (fun next member => stmtChecked next (by simp [member]))
      simpa only [Goose.Lower.lowerStmts, bind_run, active, reduceIte] using nextBuilder

end Goose.Lower.Validation

import Goose.Lower.Validation.EmittedTypingSourceResults
import Goose.Lower.Validation.EmittedTypingBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem emitted_checked_generated_lowerBlock {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (generated : GeneratedBuilderState before)
    (loop : Option LoopCtx) (loopBounds : LoopBuilderTargets loop before)
    (loopTypes : EmittedLoopTypes loop before) (pre : List (SlotId × ValueId × OriginId))
    (preBounds : ∀ slot value origin, (slot, value, origin) ∈ pre → value < before.vals.size)
    (want : Bool) (scope : ScopeId) (stmts : List Stmt) (value : Option Expr)
    (stmtsChecked : ∀ initial before, EmittedBuilder le initial before → GeneratedBuilderState before →
      EmittedLoopTypes loop before → LoopBuilderTargets loop before →
      EmittedBuilder le initial (Goose.Lower.lowerStmts loop stmts le before).2 ∧
      GeneratedBuilderState (Goose.Lower.lowerStmts loop stmts le before).2)
    (valueChecked : ∀ initial before, EmittedBuilder le initial before → GeneratedBuilderState before →
      EmittedBuilder le initial (Goose.Lower.lowerBlockValue want value le before).2 ∧
      GeneratedBuilderState (Goose.Lower.lowerBlockValue want value le before).2) :
    let after := (Goose.Lower.lowerBlock loop pre want (.mk scope stmts value) le before).2
    EmittedBuilder le initial after ∧ GeneratedBuilderState after := by
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
  have enteredGenerated := generated.emitEffect (.enter scope) (show emitEffect (.enter scope) le before = entered from rfl)
  have pushedGenerated : GeneratedBuilderState pushed.2 :=
    ⟨enteredGenerated.dense, enteredGenerated.live, enteredGenerated.targets⟩
  have initializedGenerated := pushedGenerated.initSlots pre (show initSlots pre le pushed.2 = initialized from rfl)
  have initializedGrowth : before.blocks.size ≤ initialized.2.blocks.size := by
    have enterGrowth : before.blocks.size ≤ entered.2.blocks.size := (advB_emitEffect (.enter scope) le before _ _ (show emitEffect (.enter scope) le before = entered from rfl)).ext.1
    have initGrowth : pushed.2.blocks.size ≤ initialized.2.blocks.size := (advB_initSlots pre le pushed.2 _ _ (show initSlots pre le pushed.2 = initialized from rfl)).ext.1
    have pushSize : pushed.2.blocks.size = entered.2.blocks.size := rfl
    nat_omega
  have statementsBuilder := stmtsChecked initial initialized.2 initializedBuilder initializedGenerated
    (loopTypes.retained initializedTypes) (loopBounds.mono initializedGrowth)
  have outputBuilder := valueChecked initial statements.2 statementsBuilder.1 statementsBuilder.2
  have leftBuilder := outputBuilder.1.emitEffect (.leave scope)
    (by intro active operand member; simp [Effect.uses] at member)
  have poppedBuilder := leftBuilder.popScope
  have leftGenerated := outputBuilder.2.emitEffect (.leave scope)
    (show emitEffect (.leave scope) le output.2 = left from rfl)
  have poppedGenerated : GeneratedBuilderState (popScope le left.2).2 :=
    ⟨leftGenerated.dense, leftGenerated.live, leftGenerated.targets⟩
  simpa only [Goose.Lower.lowerBlock, Goose.Lower.inScope, bind_run, pure_run,
    entered, pushed, initialized, statements, output, left] using And.intro poppedBuilder poppedGenerated

theorem emitted_checked_generated_lowerStmts {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (generated : GeneratedBuilderState before)
    (loop : Option LoopCtx) (loopBounds : LoopBuilderTargets loop before)
    (loopTypes : EmittedLoopTypes loop before) (stmts : List Stmt)
    (stmtChecked : ∀ stmt ∈ stmts, ∀ initial before,
      EmittedBuilder le initial before → GeneratedBuilderState before → EmittedLoopTypes loop before →
      LoopBuilderTargets loop before → before.cur.isSome = true →
      EmittedBuilder le initial (Goose.Lower.lowerStmt loop stmt le before).2 ∧
      GeneratedBuilderState (Goose.Lower.lowerStmt loop stmt le before).2) :
    let after := (Goose.Lower.lowerStmts loop stmts le before).2
    EmittedBuilder le initial after ∧ GeneratedBuilderState after := by
  induction stmts generalizing before with
  | nil => exact ⟨builder, generated⟩
  | cons stmt rest inductionHypothesis =>
    cases live : before.cur with
    | none =>
      have active : Goose.Lower.isLive le before = (false, before) := isLive_none live
      simpa only [Goose.Lower.lowerStmts, bind_run, active, Bool.false_eq_true, reduceIte, pure_run] using And.intro builder generated
    | some block =>
      have active : Goose.Lower.isLive le before = (true, before) := by
        simp [Goose.Lower.isLive, Goose.Lower.curBlock, bind_run, live, pure_run]
      have stmtBuilder := stmtChecked stmt (by simp) initial before builder generated loopTypes loopBounds (by rw [live]; rfl)
      have nextTypes := loopTypes.retained (types_lowerStmt loop stmt le before _ _ rfl)
      have nextBounds := loopBounds.mono (advB_lowerStmt loop stmt le before _ _ rfl).ext.1
      have nextBuilder := inductionHypothesis stmtBuilder.1 stmtBuilder.2 nextBounds nextTypes (fun next member => stmtChecked next (by simp [member]))
      simpa only [Goose.Lower.lowerStmts, bind_run, active, reduceIte] using nextBuilder

end Goose.Lower.Validation

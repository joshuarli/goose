import Goose.Lower.Validation.EmittedTypingGeneratedBlocks
import Goose.Lower.Validation.SourceEnvironment

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_checked_source_statements {results : List Ty} (stmts : List Stmt)
    {env next : Core.TEnv} {scope start finish : Nat}
    (source : Core.tyStmts env scope stmts start = .ok (next, finish))
    (children : ∀ stmt ∈ stmts, ∀ {env next : Core.TEnv} {start finish : Nat},
      Core.tyStmt env scope stmt start = .ok (next, finish) →
      ∀ {initial before : LS} (loop : Option LoopCtx), GeneratedBuilderState before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
      EmittedLoopTypes loop before → LoopBuilderTargets loop before → before.cur.isSome = true →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial
        (lowerStmt loop stmt (lowerEnv env.mod env.vars results) before).2 ∧
      GeneratedBuilderState (lowerStmt loop stmt (lowerEnv env.mod env.vars results) before).2)
    {initial before : LS} (loop : Option LoopCtx) (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before)
    (loopTypes : EmittedLoopTypes loop before) (loopBounds : LoopBuilderTargets loop before) :
    let after := (lowerStmts loop stmts (lowerEnv env.mod env.vars results) before).2
    EmittedBuilder (lowerEnv env.mod env.vars results) initial after ∧ GeneratedBuilderState after := by
  induction stmts generalizing env start before with
  | nil => exact ⟨builder, generated⟩
  | cons stmt rest inductionHypothesis =>
    obtain ⟨middle, middleStart, stmtSource, restSource⟩ := (st_bind_ok _ _ _ _).mp source
    have tables := tyStmt_tables stmt stmtSource
    have sameEnv : lowerEnv middle.mod middle.vars results = lowerEnv env.mod env.vars results := by
      rw [tables.1, tables.2.1]
    cases live : before.cur with
    | none =>
      have stopped := isLive_none (le := lowerEnv env.mod env.vars results) live
      simpa only [lowerStmts, bind_run, stopped, Bool.false_eq_true, reduceIte, pure_run] using
        And.intro builder generated
    | some block =>
      have active : Goose.Lower.isLive (lowerEnv env.mod env.vars results) before = (true, before) := by
        simp [Goose.Lower.isLive, Goose.Lower.curBlock, bind_run, live, pure_run]
      have stmtProof := children stmt (by simp) stmtSource loop generated builder loopTypes loopBounds (by simp [live])
      have nextTypes := loopTypes.retained (types_lowerStmt loop stmt (lowerEnv env.mod env.vars results) before _ _ rfl)
      have nextBounds := loopBounds.mono (advB_lowerStmt loop stmt (lowerEnv env.mod env.vars results) before _ _ rfl).ext.1
      have restProof := inductionHypothesis restSource (fun stmt member => children stmt (by simp [member]))
        stmtProof.2 (by simpa only [sameEnv] using stmtProof.1) nextTypes nextBounds
      simpa only [lowerStmts, bind_run, active, reduceIte, sameEnv] using restProof

end Goose.Lower.Validation

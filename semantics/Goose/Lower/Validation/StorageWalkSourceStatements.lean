import Goose.Lower.Validation.StorageWalkSourceContracts
import Goose.Lower.Validation.SourceStatementTypingBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem storageWalk_source_statements (scope : ScopeId) (stmts : List Stmt)
    {results : List Ty} {stack : List ScopeId}
    (children : ∀ stmt ∈ stmts, ∀ env, StorageWalkSourceStatement env results stack scope stmt)
    {env output : Core.TEnv} {start finish : Nat}
    (source : Core.tyStmts env scope stmts start = .ok (output, finish))
    (visible : StorageWalkVisible env stack) (active : scope ∈ stack) (loop : Option LoopCtx) :
    StorageWalkAction (lowerEnv env.mod env.vars results).slots stack loop (lowerStmts loop stmts) := by
  induction stmts generalizing env start with
  | nil => exact StorageWalkAction.pure _ stack loop ()
  | cons stmt rest ih =>
    obtain ⟨middle, next, first, remaining⟩ := tyStmts_cons_children source
    have head := children stmt (by simp) env first visible active loop
    have tail := ih (fun child member => children child (by simp [member])) remaining
      (visible.tyStmt active first)
    have same := tyStmt_tables stmt first
    rw [same.1, same.2.1] at tail
    unfold lowerStmts
    refine (StorageWalkAction.isLive _ stack loop).bind fun live => ?_
    cases live
    · exact StorageWalkAction.pure _ stack loop ()
    · exact head.bind fun _ => tail

#print axioms storageWalk_source_statements

end Goose.Lower.Validation

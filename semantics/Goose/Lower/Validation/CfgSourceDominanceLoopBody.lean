import Goose.Lower.Validation.CfgSourceDominanceHeader

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ssa_loopBody (continuation : ContKind) (condition : ValueId) (bodyInputs : List ValueId)
    {body : Nat → BlockId → B ValueId} {back : B Unit}
    (bodySource : ∀ depth exit, SSARun (some ⟨depth, exit, continuation⟩) bodyInputs (fun _ => []) (body depth exit))
    (backSource : ∀ depth exit, SSARun (some ⟨depth, exit, continuation⟩) [] (fun _ => []) back)
    {env : LEnv} {before after : LS} {result : Unit} {source : BlockId}
    (run : loopBody condition body back env before = (result, after))
    (imports : ImportedValues) (checked : ImportedState before imports)
    (current : before.cur = some source) (header : HeaderSSA continuation before imports)
    (operands : AvailableValues before imports [condition]) (inputs : AvailableValues before imports bodyInputs) :
    ∃ nextImports, SSAResult before after imports nextImports [] := by
  unfold loopBody at run
  obtain ⟨state, first, readRun, ⟨bodyBlock, exitBlock⟩, forked, forkRun, _, started, startRun,
    bodyValue, bodyEnd, bodyRun, _, backEnd, backRun, exitRun⟩ := (by simpa only [bind_eq] using run)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj readRun
  obtain ⟨ids, _⟩ := fork_ids forkRun
  obtain ⟨bodyId, exitId⟩ := Prod.mk.inj ids
  subst bodyId exitId
  obtain ⟨forkImports, forkState⟩ := ssa_fork condition env before imports checked current operands
  rw [forkRun] at forkState
  have selected := forkState.select forkState.firstBound forkState.firstFresh
    forkState.firstOpen forkState.firstImports env
  rw [startRun] at selected
  have exitBoundStarted : before.blocks.size + 1 < started.blocks.size := by
    simpa only [← setCur_blocks startRun] using forkState.secondBound
  have exitAvailable : AvailableValues started forkImports (forkImports (before.blocks.size + 1)) := by
    rw [forkState.secondImports]
    exact selected.frame _ (currentValues_available checked.opened.bound)
  have ready := (header.move selected).loopReady before.stack.length (before.blocks.size + 1)
    exitBoundStarted exitAvailable
  obtain ⟨bodyImports, bodyState⟩ := bodySource before.stack.length (before.blocks.size + 1)
    env started bodyValue bodyEnd bodyRun forkImports selected.checked ready (selected.frame bodyInputs inputs)
  obtain ⟨nextImports, backState⟩ := backSource before.stack.length (before.blocks.size + 1)
    env bodyEnd _ backEnd backRun bodyImports bodyState.checked (bodyState.loop ready) (by simp [AvailableValues])
  have history := selected.trans (bodyState.trans backState)
  have bodyExitBound := Nat.lt_of_lt_of_le exitBoundStarted bodyState.advance.ext.1
  have backExitBound := Nat.lt_of_lt_of_le bodyExitBound backState.advance.ext.1
  have exitImports : nextImports (before.blocks.size + 1) = currentValues before imports :=
    (backState.imports _ bodyExitBound).trans ((bodyState.imports _ exitBoundStarted).trans forkState.secondImports)
  have notCurrent : started.cur ≠ some (before.blocks.size + 1) := by
    have selectedCurrent : started.cur = some before.blocks.size := by
      rw [setCur_run] at startRun
      exact congrArg LS.cur (Prod.mk.inj startRun).2.symm
    rw [selectedCurrent]
    exact fun equal => Nat.ne_of_lt (Nat.lt_succ_self _) (Option.some.inj equal)
  obtain ⟨exitBody, forkRow, exitOpen⟩ := forkState.secondOpen
  have startRow : started.blocks[before.blocks.size + 1]? = some exitBody := by
    simpa only [← setCur_blocks startRun] using forkRow
  have bodyRow := bodyState.advance.keep _ _ notCurrent startRow
  have backRow := backState.advance.keep _ _
    (advance_current_ne_old bodyState.advance exitBoundStarted notCurrent) bodyRow
  have finished := SSAResult.select_imports backState.checked history.advance history.imports
    (by simp [current]) backExitBound (Nat.le_succ _) ⟨_, backRow, exitOpen⟩ exitImports env
  rw [exitRun] at finished
  exact ⟨nextImports, finished⟩

end Goose.Lower.Validation

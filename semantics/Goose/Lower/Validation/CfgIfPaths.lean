import Goose.Lower.Validation.CfgControlPaths

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem paths_ifE_core (condition : ValueId) (sourceScope : ScopeId) {thenAction elseAction : B ValueId}
    (thenAdvance : AdvB thenAction) (elseAdvance : AdvB elseAction)
    (thenPaths : BoundedRun ReachableBuilder thenAction)
    (elsePaths : BoundedRun ReachableBuilder elseAction) :
    BoundedRun ReachableBuilder (whenLive 0 fun _ => do
      let (thenBlock, elseBlock) ← fork condition
      setCur (some thenBlock)
      let thenValue ← thenAction
      let endThen ← curBlock
      setCur (some elseBlock)
      let elseValue ← elseAction
      let endElse ← curBlock
      let value ← joinValue endThen thenValue endElse elseValue
      recordValueRootRecipe value sourceScope
      pure value) := by
  intro env before result after run paths bounded
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact paths
  | some source =>
    rw [whenLive_some _ _ env current] at run
    simp only [bind_eq] at run
    obtain ⟨⟨thenBlock, elseBlock⟩, forked, forkRun, _, thenStart, thenStartRun,
      thenValue, thenEnd, thenRun, endThen, thenRead, thenReadRun,
      _, elseStart, elseStartRun, elseValue, elseEnd, elseRun,
      endElse, elseRead, elseReadRun, joinedValue, joinState, joinRun,
      _, recipeState, recipeRun, pureRun⟩ := run
    obtain ⟨thenCurrent, thenSame⟩ := curBlock_eq thenReadRun
    obtain ⟨elseCurrent, elseSame⟩ := curBlock_eq elseReadRun
    subst thenRead
    subst elseRead
    have forkPaths := paths.fork current (bounded source current) condition env
    have forkBounds := liveBound_fork current condition env
    rw [forkRun] at forkPaths forkBounds
    dsimp only at forkPaths forkBounds
    have thenStartPaths := forkPaths.of_blocks (setCur_blocks thenStartRun)
    have thenStartBound := liveBound_setCur forkBounds.1 env
    rw [thenStartRun] at thenStartBound
    have thenEndPaths := thenPaths env thenStart thenValue thenEnd thenRun thenStartPaths thenStartBound
    have thenGrowth := thenAdvance env thenStart thenValue thenEnd thenRun
    have thenEndBound := liveBound_of_adv thenGrowth thenStartBound
    have forkToThen : forked.blocks.size ≤ thenEnd.blocks.size := by
      have growth := thenGrowth.ext.1
      rw [setCur_blocks thenStartRun] at growth
      exact growth
    have elseBlockBound := Nat.lt_of_lt_of_le forkBounds.2 forkToThen
    have elseStartPaths := thenEndPaths.of_blocks (setCur_blocks elseStartRun)
    have elseStartBound := liveBound_setCur elseBlockBound env
    rw [elseStartRun] at elseStartBound
    have elseEndPaths := elsePaths env elseStart elseValue elseEnd elseRun elseStartPaths elseStartBound
    have elseGrowth := elseAdvance env elseStart elseValue elseEnd elseRun
    have elseEndBound := liveBound_of_adv elseGrowth elseStartBound
    have thenToElse : thenEnd.blocks.size ≤ elseEnd.blocks.size := by
      have growth := elseGrowth.ext.1
      rw [setCur_blocks elseStartRun] at growth
      exact growth
    have thenBound : ∀ block, endThen = some block → block < elseEnd.blocks.size := by
      intro block present
      exact Nat.lt_of_lt_of_le (thenEndBound block (thenCurrent.symm.trans present)) thenToElse
    have elseBound : ∀ block, endElse = some block → block < elseEnd.blocks.size := by
      intro block present
      exact elseEndBound block (elseCurrent.symm.trans present)
    have joined := elseEndPaths.joinValue endThen endElse thenValue elseValue thenBound elseBound env
    rw [joinRun] at joined
    rw [recordValueRootRecipe_run] at recipeRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj recipeRun
    rw [pure_run] at pureRun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pureRun
    exact joined.of_blocks (by simp)

theorem paths_ifS_some_core (condition : ValueId) {thenAction elseAction : B ValueId}
    (thenAdvance : AdvB thenAction) (elseAdvance : AdvB elseAction)
    (thenPaths : BoundedRun ReachableBuilder thenAction)
    (elsePaths : BoundedRun ReachableBuilder elseAction) :
    BoundedRun ReachableBuilder (whenLive () fun _ => do
      let (thenBlock, elseBlock) ← fork condition
      setCur (some thenBlock)
      let _ ← thenAction
      let endThen ← curBlock
      setCur (some elseBlock)
      let _ ← elseAction
      let endElse ← curBlock
      joinArms endThen endElse) := by
  intro env before result after run paths bounded
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact paths
  | some source =>
    rw [whenLive_some _ _ env current] at run
    simp only [bind_eq] at run
    obtain ⟨⟨thenBlock, elseBlock⟩, forked, forkRun, _, thenStart, thenStartRun,
      thenValue, thenEnd, thenRun, endThen, thenRead, thenReadRun,
      _, elseStart, elseStartRun, elseValue, elseEnd, elseRun,
      endElse, elseRead, elseReadRun, joinRun⟩ := run
    obtain ⟨thenCurrent, thenSame⟩ := curBlock_eq thenReadRun
    obtain ⟨elseCurrent, elseSame⟩ := curBlock_eq elseReadRun
    subst thenRead
    subst elseRead
    have forkPaths := paths.fork current (bounded source current) condition env
    have forkBounds := liveBound_fork current condition env
    rw [forkRun] at forkPaths forkBounds
    dsimp only at forkPaths forkBounds
    have thenStartPaths := forkPaths.of_blocks (setCur_blocks thenStartRun)
    have thenStartBound := liveBound_setCur forkBounds.1 env
    rw [thenStartRun] at thenStartBound
    have thenEndPaths := thenPaths env thenStart thenValue thenEnd thenRun thenStartPaths thenStartBound
    have thenGrowth := thenAdvance env thenStart thenValue thenEnd thenRun
    have thenEndBound := liveBound_of_adv thenGrowth thenStartBound
    have forkToThen : forked.blocks.size ≤ thenEnd.blocks.size := by
      have growth := thenGrowth.ext.1
      rw [setCur_blocks thenStartRun] at growth
      exact growth
    have elseBlockBound := Nat.lt_of_lt_of_le forkBounds.2 forkToThen
    have elseStartPaths := thenEndPaths.of_blocks (setCur_blocks elseStartRun)
    have elseStartBound := liveBound_setCur elseBlockBound env
    rw [elseStartRun] at elseStartBound
    have elseEndPaths := elsePaths env elseStart elseValue elseEnd elseRun elseStartPaths elseStartBound
    have elseGrowth := elseAdvance env elseStart elseValue elseEnd elseRun
    have elseEndBound := liveBound_of_adv elseGrowth elseStartBound
    have thenToElse : thenEnd.blocks.size ≤ elseEnd.blocks.size := by
      have growth := elseGrowth.ext.1
      rw [setCur_blocks elseStartRun] at growth
      exact growth
    have thenBound : ∀ block, endThen = some block → block < elseEnd.blocks.size := by
      intro block present
      exact Nat.lt_of_lt_of_le (thenEndBound block (thenCurrent.symm.trans present)) thenToElse
    have elseBound : ∀ block, endElse = some block → block < elseEnd.blocks.size := by
      intro block present
      exact elseEndBound block (elseCurrent.symm.trans present)
    have joined := elseEndPaths.joinArms endThen endElse thenBound elseBound env
    rw [joinRun] at joined
    exact joined

theorem paths_ifS_none_core (condition : ValueId) {childAction : B ValueId}
    (child : BoundedRun ReachableBuilder childAction) :
    BoundedRun ReachableBuilder (whenLive () fun _ => do
      let (thenBlock, joinBlock) ← fork condition
      setCur (some thenBlock)
      let _ ← childAction
      emitTerm (.br joinBlock [])
      setCur (some joinBlock)) := by
  intro env before result after run paths bounded
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact paths
  | some source =>
    rw [whenLive_some _ _ env current] at run
    simp only [bind_eq] at run
    obtain ⟨⟨thenBlock, joinBlock⟩, forked, forkRun, _, started, startRun,
      value, childEnd, childRun, _, closed, closeRun, joinRun⟩ := run
    have forkPaths := paths.fork current (bounded source current) condition env
    have forkBounds := liveBound_fork current condition env
    rw [forkRun] at forkPaths forkBounds
    dsimp only at forkPaths forkBounds
    have startedPaths := forkPaths.of_blocks (setCur_blocks startRun)
    have startedBound := liveBound_setCur forkBounds.1 env
    rw [startRun] at startedBound
    have childPaths := child env started value childEnd childRun startedPaths startedBound
    have closedPaths := childPaths.emitTerm (.br joinBlock []) env
    rw [closeRun] at closedPaths
    exact closedPaths.of_blocks (setCur_blocks joinRun)

end Goose.Lower.Validation

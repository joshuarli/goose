import Goose.Lower.Validation.CfgOpenTargets

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem setCur_current {current : Option BlockId} {env : LEnv} {before after : LS} {result : Unit}
    (run : setCur current env before = (result, after)) : after.cur = current := by
  rw [setCur_run] at run
  exact congrArg LS.cur (Prod.mk.inj run).2.symm

theorem restore_currentOpen {before middle after : LS} {block : BlockId} {body : BlockB}
    (row : before.blocks[block]? = some body) (openBody : OpenBlock body)
    (different : before.cur ≠ some block) (advance : before.Adv middle)
    {env : LEnv} {result : Unit} (restore : setCur (some block) env middle = (result, after)) :
    CurrentOpen after := by
  have preserved := advance.keep block body different row
  have openCurrent := CurrentOpen.setCur preserved openBody env
  rw [restore] at openCurrent
  exact openCurrent

theorem fork_distinct {state : LS} {source : BlockId} (current : state.cur = some source)
    {condition : ValueId} {env : LEnv} {pair : BlockId × BlockId} {after : LS}
    (run : fork condition env state = (pair, after)) : pair.1 ≠ pair.2 := by
  rw [fork_run condition env current] at run
  obtain ⟨rfl, _⟩ := Prod.mk.inj run
  simp

theorem opens_shortCircuit (isAnd : Bool) (value : ValueId) {rhs : B ValueId} (child : AdvB rhs) :
    BoundedRun CurrentOpen (shortCircuit isAnd value rhs) := by
  intro env before result after run _ bounded
  cases current : before.cur with
  | none =>
    rw [shortCircuit, whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact currentOpen_none current
  | some source =>
    rw [shortCircuit, whenLive_some _ _ env current] at run
    obtain ⟨pair, forked, forkRun, run⟩ := bind_eq.mp run
    obtain ⟨_, started, startRun, run⟩ := bind_eq.mp run
    obtain ⟨_, childAfter, childRun, run⟩ := bind_eq.mp run
    obtain ⟨_, closed, closeRun, run⟩ := bind_eq.mp run
    obtain ⟨_, joined, joinRun, run⟩ := bind_eq.mp run
    obtain ⟨_, stateEqual⟩ := pure_eq.mp run
    have targets := scFork_open_targets current (bounded source current) isAnd value env
    rw [forkRun] at targets
    obtain ⟨body, row, openBody⟩ := targets.2
    have startedRow : started.blocks[pair.2.1]? = some body := by
      simpa [setCur_blocks startRun] using row
    have ids := (scFork_ids forkRun).1
    have distinct : pair.1 ≠ pair.2.1 := by rw [ids]; simp
    have different : started.cur ≠ some pair.2.1 := by
      rw [setCur_current startRun]
      exact fun equality => distinct (Option.some.inj equality)
    have advanced := (child env started _ childAfter childRun).trans (adv_emitTerm closeRun)
    have joinedOpen := restore_currentOpen startedRow openBody different advanced joinRun
    rw [← stateEqual]
    exact joinedOpen

theorem opens_ifS_none_core (condition : ValueId) {childAction : B ValueId} (child : AdvB childAction) :
    BoundedRun CurrentOpen (whenLive () fun _ => do
      let (thenBlock, joinBlock) ← fork condition
      setCur (some thenBlock)
      let _ ← childAction
      emitTerm (.br joinBlock [])
      setCur (some joinBlock)) := by
  intro env before result after run _ bounded
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact currentOpen_none current
  | some source =>
    rw [whenLive_some _ _ env current] at run
    simp only [bind_eq] at run
    obtain ⟨⟨thenBlock, joinBlock⟩, forked, forkRun, _, started, startRun,
      value, childEnd, childRun, _, closed, closeRun, joinRun⟩ := run
    have targets := fork_open_targets current (bounded source current) condition env
    rw [forkRun] at targets
    obtain ⟨body, row, openBody⟩ := targets.2
    have startedRow : started.blocks[joinBlock]? = some body := by
      simpa [setCur_blocks startRun] using row
    have distinct := fork_distinct current forkRun
    have different : started.cur ≠ some joinBlock := by
      rw [setCur_current startRun]
      exact fun equality => distinct (Option.some.inj equality)
    exact restore_currentOpen startedRow openBody different
      ((child env started value childEnd childRun).trans (adv_emitTerm closeRun)) joinRun

theorem opens_ifE_core (condition : ValueId) {thenAction elseAction : B ValueId}
    (thenAdvance : AdvB thenAction) (elseAdvance : AdvB elseAction)
    :
    BoundedRun CurrentOpen (whenLive 0 fun _ => do
      let (thenBlock, elseBlock) ← fork condition
      setCur (some thenBlock)
      let thenValue ← thenAction
      let endThen ← curBlock
      setCur (some elseBlock)
      let elseValue ← elseAction
      let endElse ← curBlock
      joinValue endThen thenValue endElse elseValue) := by
  intro env before result after run _ bounded
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact currentOpen_none current
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
    have forkBounds := liveBound_fork current condition env
    rw [forkRun] at forkBounds
    dsimp only at forkBounds
    have thenStartBound := liveBound_setCur forkBounds.1 env
    rw [thenStartRun] at thenStartBound
    have thenGrowth := thenAdvance env thenStart thenValue thenEnd thenRun
    have thenEndBound := liveBound_of_adv thenGrowth thenStartBound
    have forkToThen : forked.blocks.size ≤ thenEnd.blocks.size := by
      have growth := thenGrowth.ext.1
      rw [setCur_blocks thenStartRun] at growth
      exact growth
    have elseBlockBound := Nat.lt_of_lt_of_le forkBounds.2 forkToThen
    have elseStartBound := liveBound_setCur elseBlockBound env
    rw [elseStartRun] at elseStartBound
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
    have joined := joinValue_currentOpen elseEnd endThen endElse thenValue elseValue thenBound elseBound env
    rw [joinRun] at joined
    exact joined

theorem opens_ifS_some_core (condition : ValueId) {thenAction elseAction : B ValueId}
    (thenAdvance : AdvB thenAction) (elseAdvance : AdvB elseAction)
    :
    BoundedRun CurrentOpen (whenLive () fun _ => do
      let (thenBlock, elseBlock) ← fork condition
      setCur (some thenBlock)
      let _ ← thenAction
      let endThen ← curBlock
      setCur (some elseBlock)
      let _ ← elseAction
      let endElse ← curBlock
      joinArms endThen endElse) := by
  intro env before result after run _ bounded
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact currentOpen_none current
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
    have forkBounds := liveBound_fork current condition env
    rw [forkRun] at forkBounds
    dsimp only at forkBounds
    have thenStartBound := liveBound_setCur forkBounds.1 env
    rw [thenStartRun] at thenStartBound
    have thenGrowth := thenAdvance env thenStart thenValue thenEnd thenRun
    have thenEndBound := liveBound_of_adv thenGrowth thenStartBound
    have forkToThen : forked.blocks.size ≤ thenEnd.blocks.size := by
      have growth := thenGrowth.ext.1
      rw [setCur_blocks thenStartRun] at growth
      exact growth
    have elseBlockBound := Nat.lt_of_lt_of_le forkBounds.2 forkToThen
    have elseStartBound := liveBound_setCur elseBlockBound env
    rw [elseStartRun] at elseStartBound
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
    have joined := joinArms_currentOpen elseEnd endThen endElse thenBound elseBound env
    rw [joinRun] at joined
    exact joined


end Goose.Lower.Validation

import Goose.Lower.Validation.CfgForkCompletion
import Goose.Lower.Validation.CfgJoinCompletion

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem complete_shortCircuit (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (child : CompletionAction rhs) : CompletionAction (shortCircuit isAnd value rhs) := by
  refine ⟨⟨advB_shortCircuit isAnd value child.openAction.advance,
    opens_shortCircuit isAnd value child.openAction.advance⟩, ?_⟩
  intro env before result after run openBefore shapedBefore
  cases current : before.cur with
  | none =>
    rw [shortCircuit, whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨shapedBefore, rfl⟩
  | some source =>
    rw [shortCircuit, whenLive_some _ _ env current] at run
    obtain ⟨pair, forked, forkRun, run⟩ := bind_eq.mp run
    obtain ⟨_, started, startRun, run⟩ := bind_eq.mp run
    obtain ⟨rhsValue, childAfter, childRun, run⟩ := bind_eq.mp run
    obtain ⟨_, closed, closeRun, run⟩ := bind_eq.mp run
    obtain ⟨_, joined, joinRun, run⟩ := bind_eq.mp run
    obtain ⟨_, stateEqual⟩ := pure_eq.mp run
    subst after
    have targets := scFork_open_targets current (openBefore.bound source current) isAnd value env
    rw [forkRun] at targets
    obtain ⟨body, row, openBody⟩ := targets.1
    have openStarted := CurrentOpen.setCur row openBody env
    rw [startRun] at openStarted
    obtain ⟨shapeFork, countFork⟩ := scFork_complete current openBefore shapedBefore isAnd value env
    rw [forkRun] at shapeFork countFork
    have shapeStarted := shapeFork.of_blocks (setCur_blocks startRun)
    obtain ⟨shapeChild, countChild⟩ := child.complete env started _ childAfter childRun openStarted shapeStarted
    have openChild := child.openAction.paths env started _ childAfter childRun openStarted openStarted.bound
    obtain ⟨shapeClosed, countClosed⟩ := (complete_emitTerm _).complete
      env childAfter _ closed closeRun openChild shapeChild
    refine ⟨shapeClosed.of_blocks (setCur_blocks joinRun), ?_⟩
    have startCount : OpenCount started = OpenCount forked := by simp only [OpenCount, setCur_blocks startRun]
    have joinCount : OpenCount joined = OpenCount closed := by simp only [OpenCount, setCur_blocks joinRun]
    have liveBefore : LiveCount before = 1 := by simp [LiveCount, current]
    have liveStarted : LiveCount started = 1 := by simp [LiveCount, setCur_current startRun]
    have liveJoined : LiveCount joined = 1 := by simp [LiveCount, setCur_current joinRun]
    have liveClosed : LiveCount closed = 0 := by
      have stopped := emitTerm_stopped (.br pair.2.1 [rhsValue]) env childAfter
      rw [closeRun] at stopped
      dsimp only at stopped
      simp [LiveCount, stopped]
    dsimp only at countFork
    omega

theorem complete_ifS_none (condition : ValueId) {rhs : B ValueId}
    (child : CompletionAction rhs) : CompletionAction (whenLive () fun _ => do
      let (thenBlock, joinBlock) ← fork condition
      setCur (some thenBlock)
      let _ ← rhs
      emitTerm (.br joinBlock [])
      setCur (some joinBlock)) := by
  refine ⟨⟨advB_ifS_none_core condition child.openAction.advance,
    opens_ifS_none_core condition child.openAction.advance⟩, ?_⟩
  intro env before result after run openBefore shapedBefore
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨shapedBefore, rfl⟩
  | some source =>
    rw [whenLive_some _ _ env current] at run
    obtain ⟨pair, forked, forkRun, run⟩ := bind_eq.mp run
    obtain ⟨_, started, startRun, run⟩ := bind_eq.mp run
    obtain ⟨rhsValue, childAfter, childRun, run⟩ := bind_eq.mp run
    obtain ⟨_, closed, closeRun, run⟩ := bind_eq.mp run
    have joinRun := run
    have targets := fork_open_targets current (openBefore.bound source current) condition env
    rw [forkRun] at targets
    obtain ⟨body, row, openBody⟩ := targets.1
    have openStarted := CurrentOpen.setCur row openBody env
    rw [startRun] at openStarted
    obtain ⟨shapeFork, countFork⟩ := fork_complete current openBefore shapedBefore condition env
    rw [forkRun] at shapeFork countFork
    have shapeStarted := shapeFork.of_blocks (setCur_blocks startRun)
    obtain ⟨shapeChild, countChild⟩ := child.complete env started _ childAfter childRun openStarted shapeStarted
    have openChild := child.openAction.paths env started _ childAfter childRun openStarted openStarted.bound
    obtain ⟨shapeClosed, countClosed⟩ := (complete_emitTerm _).complete
      env childAfter _ closed closeRun openChild shapeChild
    refine ⟨shapeClosed.of_blocks (setCur_blocks joinRun), ?_⟩
    have startCount : OpenCount started = OpenCount forked := by simp only [OpenCount, setCur_blocks startRun]
    have joinCount : OpenCount after = OpenCount closed := by simp only [OpenCount, setCur_blocks joinRun]
    have liveBefore : LiveCount before = 1 := by simp [LiveCount, current]
    have liveStarted : LiveCount started = 1 := by simp [LiveCount, setCur_current startRun]
    have liveJoined : LiveCount after = 1 := by simp [LiveCount, setCur_current joinRun]
    have liveClosed : LiveCount closed = 0 := by
      have stopped := emitTerm_stopped (.br pair.2 []) env childAfter
      rw [closeRun] at stopped
      dsimp only at stopped
      simp [LiveCount, stopped]
    dsimp only at countFork
    omega

theorem complete_assert (condition : ValueId) (origin : OriginId) :
    CompletionAction (whenLive () fun _ => do
      let (passBlock, failBlock) ← fork condition
      setCur (some failBlock)
      emitTerm (.abort .assert (some origin))
      setCur (some passBlock)) := by
  refine ⟨open_assert condition origin, ?_⟩
  intro env before result after run openBefore shapedBefore
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨shapedBefore, rfl⟩
  | some source =>
    rw [whenLive_some _ _ env current] at run
    simp only [bind_eq] at run
    obtain ⟨⟨passBlock, failBlock⟩, forked, forkRun, _, started, startRun,
      _, closed, closeRun, finalRun⟩ := run
    have targets := fork_open_targets current (openBefore.bound source current) condition env
    rw [forkRun] at targets
    obtain ⟨body, row, openBody⟩ := targets.2
    have openStarted := CurrentOpen.setCur row openBody env
    rw [startRun] at openStarted
    obtain ⟨shapeFork, countFork⟩ := fork_complete current openBefore shapedBefore condition env
    rw [forkRun] at shapeFork countFork
    have shapeStarted := shapeFork.of_blocks (setCur_blocks startRun)
    obtain ⟨shapeClosed, countClosed⟩ := (complete_emitTerm (.abort .assert (some origin))).complete
      env started _ closed closeRun openStarted shapeStarted
    refine ⟨shapeClosed.of_blocks (setCur_blocks finalRun), ?_⟩
    have startCount : OpenCount started = OpenCount forked := by simp only [OpenCount, setCur_blocks startRun]
    have finalCount : OpenCount after = OpenCount closed := by simp only [OpenCount, setCur_blocks finalRun]
    have liveBefore : LiveCount before = 1 := by simp [LiveCount, current]
    have liveStarted : LiveCount started = 1 := by simp [LiveCount, setCur_current startRun]
    have liveAfter : LiveCount after = 1 := by simp [LiveCount, setCur_current finalRun]
    have liveClosed : LiveCount closed = 0 := by
      have stopped := emitTerm_stopped (.abort .assert (some origin)) env started
      rw [closeRun] at stopped
      dsimp only at stopped
      simp [LiveCount, stopped]
    dsimp only at countFork
    omega

end Goose.Lower.Validation

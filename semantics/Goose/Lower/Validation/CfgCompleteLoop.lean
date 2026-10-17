import Goose.Lower.Validation.CfgCompleteActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem LiveCompletionRun.bind {first : B α} {next : α → B β}
    (child : CompletionAction first) (current : ∀ env state, (first env state).2.cur = state.cur)
    (rest : ∀ result, LiveCompletionRun (next result)) : LiveCompletionRun (first >>= next) := by
  intro env before result after run openBefore shapedBefore live
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  obtain ⟨shapeMiddle, countFirst⟩ := child.complete env before value middle firstRun openBefore shapedBefore
  have openMiddle := child.openAction.paths env before value middle firstRun openBefore openBefore.bound
  have middleCurrent := current env before
  rw [firstRun] at middleCurrent
  dsimp only at middleCurrent
  obtain ⟨shapeAfter, countNext⟩ := rest value env middle result after nextRun openMiddle shapeMiddle
    (by simpa [middleCurrent] using live)
  exact ⟨shapeAfter, by omega⟩

theorem complete_rangeBack (ty : IntTy) (counter : ValueId) (header : BlockId) :
    CompletionAction (rangeBack ty counter header) := by
  unfold rangeBack
  refine CompletionAction.bind complete_isLive fun live => ?_
  cases live
  · exact CompletionAction.pure _
  · exact CompletionAction.bind (complete_emitDef _) fun _ => complete_emitTerm _

theorem rangeBack_stopped (ty : IntTy) (counter : ValueId) (header : BlockId) (env : LEnv) (state : LS) :
    (rangeBack ty counter header env state).2.cur = none := by
  cases current : state.cur with
  | none =>
    simp only [rangeBack, bind_run, isLive_none current, Bool.false_eq_true, ite_false, pure_run]
    exact current
  | some block =>
    simp only [rangeBack, bind_run, isLive_run current, ite_true]
    exact emitTerm_stopped _ _ _

theorem complete_loopBody_live {condition : ValueId} {body : Nat → BlockId → B ValueId} {back : B Unit}
    (bodyComplete : ∀ depth exit, CompletionAction (body depth exit)) (backComplete : CompletionAction back)
    (backStops : ∀ env state, (back env state).2.cur = none) : LiveCompletionRun (loopBody condition body back) := by
  intro env before result after run openBefore shapedBefore live
  cases current : before.cur with
  | none => simp [current] at live
  | some source =>
    unfold loopBody at run
    simp only [bind_eq] at run
    obtain ⟨state, first, readRun, ⟨bodyBlock, exitBlock⟩, forked, forkRun,
      _, started, startRun, value, bodyEnd, bodyRun, _, backEnd, backRun, exitRun⟩ := run
    have same : first = before := (Prod.mk.inj readRun).2.symm
    subst first
    have targets := fork_open_targets current (openBefore.bound source current) condition env
    rw [forkRun] at targets
    obtain ⟨bodyRow, row, openBody⟩ := targets.1
    have openStarted := CurrentOpen.setCur row openBody env
    rw [startRun] at openStarted
    obtain ⟨shapeFork, countFork⟩ := fork_complete current openBefore shapedBefore condition env
    rw [forkRun] at shapeFork countFork
    have shapeStarted := shapeFork.of_blocks (setCur_blocks startRun)
    obtain ⟨shapeBody, countBody⟩ := (bodyComplete _ _).complete env started value bodyEnd bodyRun openStarted shapeStarted
    have openBodyEnd := (bodyComplete _ _).openAction.paths env started value bodyEnd bodyRun openStarted openStarted.bound
    obtain ⟨shapeBack, countBack⟩ := backComplete.complete env bodyEnd _ backEnd backRun openBodyEnd shapeBody
    refine ⟨shapeBack.of_blocks (setCur_blocks exitRun), ?_⟩
    have startCount : OpenCount started = OpenCount forked := by simp only [OpenCount, setCur_blocks startRun]
    have exitCount : OpenCount after = OpenCount backEnd := by simp only [OpenCount, setCur_blocks exitRun]
    have liveBefore : LiveCount before = 1 := by simp [LiveCount, current]
    have liveStarted : LiveCount started = 1 := by simp [LiveCount, setCur_current startRun]
    have liveAfter : LiveCount after = 1 := by simp [LiveCount, setCur_current exitRun]
    have liveBack : LiveCount backEnd = 0 := by
      have stopped := backStops env bodyEnd
      rw [backRun] at stopped
      dsimp only at stopped
      simp [LiveCount, stopped]
    dsimp only at countFork
    omega

theorem complete_lowerWhile (header : BlockId) {condition : B ValueId} {body : Nat → BlockId → B ValueId}
    (conditionComplete : CompletionAction condition) (bodyComplete : ∀ depth exit, CompletionAction (body depth exit)) :
    CompletionAction (lowerWhile header condition body) := by
  unfold lowerWhile
  refine CompletionAction.bind conditionComplete fun _ => ?_
  refine complete_whenLive () (open_whenLive () ?_ ?_) ?_
  · exact advB_loopBody _ (fun depth exit => (bodyComplete depth exit).openAction.advance) (advB_emitTerm _)
  · exact opens_loopBody_live (fun depth exit => (bodyComplete depth exit).openAction.advance) (advB_emitTerm _)
  · exact complete_loopBody_live bodyComplete (complete_emitTerm _) (emitTerm_stopped _)

theorem complete_lowerRange (ty : IntTy) (counter bound : ValueId) (header : BlockId)
    {body : Nat → BlockId → B ValueId} (bodyComplete : ∀ depth exit, CompletionAction (body depth exit)) :
    LiveCompletionRun (lowerRange ty counter bound header body) := by
  unfold lowerRange
  exact LiveCompletionRun.bind (complete_emitDef _) (emitDef_current _) fun _ =>
    complete_loopBody_live bodyComplete (complete_rangeBack _ _ _) (rangeBack_stopped _ _ _)

theorem complete_eachLen (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    CompletionAction (eachLen regrow owner sampled) := by
  unfold eachLen
  cases regrow
  · exact CompletionAction.pure _
  · exact complete_emitDef _

theorem complete_lowerEach (regrow : Bool) (owner : Option ValueId) (sampled header counter : Nat)
    {body : Nat → BlockId → B ValueId} (bodyComplete : ∀ depth exit, CompletionAction (body depth exit)) :
    LiveCompletionRun (lowerEach regrow owner sampled header counter body) := by
  unfold lowerEach
  refine LiveCompletionRun.bind (complete_eachLen _ _ _) (eachLen_current _ _ _) fun _ => ?_
  exact LiveCompletionRun.bind (complete_emitDef _) (emitDef_current _) fun _ =>
    complete_loopBody_live bodyComplete (complete_rangeBack _ _ _) (rangeBack_stopped _ _ _)

theorem complete_header0 {tail : BlockId → B Unit}
    (child : ∀ header, LiveCompletionRun (tail header)) :
    LiveCompletionRun (do
      let (header, _) ← newBlock []
      emitTerm (.br header [])
      setCur (some header)
      tail header) :=
  complete_header_live [] [] (tail := fun header _ => tail header) (fun header _ => child header)

theorem complete_header1 (ty : VTy) (value : ValueId) {tail : BlockId → ValueId → B Unit}
    (child : ∀ header counter, LiveCompletionRun (tail header counter)) :
    LiveCompletionRun (do
      let (header, params) ← newBlock [ty]
      emitTerm (.br header [value])
      setCur (some header)
      tail header (params.headD 0)) :=
  complete_header_live [ty] [value] (tail := fun header params => tail header (params.headD 0))
    (fun header params => child header (params.headD 0))

end Goose.Lower.Validation

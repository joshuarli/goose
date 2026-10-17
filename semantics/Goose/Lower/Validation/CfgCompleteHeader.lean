import Goose.Lower.Validation.CfgCompletion

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def LiveCompletionRun (action : B α) : Prop :=
  ∀ env before result after, action env before = (result, after) →
    CurrentOpen before → ShapedBlocks before → before.cur.isSome = true →
      ShapedBlocks after ∧ OpenCount after + LiveCount before = OpenCount before + LiveCount after

theorem complete_header_live (types : List VTy) (arguments : List ValueId)
    {tail : BlockId → List ValueId → B Unit}
    (child : ∀ header params, LiveCompletionRun (tail header params)) :
    LiveCompletionRun (do
      let (header, params) ← newBlock types
      emitTerm (.br header arguments)
      setCur (some header)
      tail header params) := by
  intro env before result after run openBefore shapedBefore live
  cases current : before.cur with
  | none => simp [current] at live
  | some source =>
    simp only [bind_eq] at run
    obtain ⟨⟨header, params⟩, initial, newRun, _, closed, closeRun,
      _, started, startRun, tailRun⟩ := run
    have headerEq : header = before.blocks.size :=
      (congrArg (fun output => output.1.1) newRun).symm
    have initialCur : initial.cur = before.cur :=
      (congrArg (fun output => output.2.cur) newRun).symm
    have openInitial := openBefore.newBlock types env
    have shapeInitial := shapedBefore.newBlock types env
    have countInitial := openCount_newBlock before types env
    have fresh := newBlock_open before env types
    rw [newRun] at openInitial shapeInitial countInitial fresh
    obtain ⟨body, row, openBody⟩ := fresh
    rw [← headerEq] at row
    have different : initial.cur ≠ some header := by
      rw [initialCur, current]
      intro same
      have equal := Option.some.inj same
      have bound := openBefore.bound source current
      rw [headerEq] at equal
      nat_omega
    have closedRow := (adv_emitTerm closeRun).keep header body different row
    have openStarted := CurrentOpen.setCur closedRow openBody env
    rw [startRun] at openStarted
    obtain ⟨shapeClosed, countClosed⟩ := (complete_emitTerm (.br header arguments)).complete
      env initial _ closed closeRun openInitial shapeInitial
    have shapeStarted : ShapedBlocks started := shapeClosed.of_blocks (setCur_blocks startRun)
    obtain ⟨shapeAfter, countTail⟩ := child header params env started result after tailRun openStarted shapeStarted
      (by simp [setCur_current startRun])
    refine ⟨shapeAfter, ?_⟩
    have countStarted : OpenCount started = OpenCount closed := by
      simp only [OpenCount, setCur_blocks startRun]
    have liveInitial : LiveCount initial = 1 := by simp [LiveCount, initialCur, current]
    have liveBefore : LiveCount before = 1 := by simp [LiveCount, current]
    have liveClosed : LiveCount closed = 0 := by
      have closeCur : closed.cur = none := by
        have initialCurrent : initial.cur = some source := initialCur.trans current
        rw [emitTerm_run _ env initialCurrent] at closeRun
        exact (congrArg (fun output => output.2.cur) closeRun).symm
      simp [LiveCount, closeCur]
    have liveStarted : LiveCount started = 1 := by simp [LiveCount, setCur_current startRun]
    dsimp only at countInitial
    omega

theorem complete_header (types : List VTy) (arguments : List ValueId)
    {tail : BlockId → List ValueId → B Unit}
    (child : ∀ header params, CompletionRun (tail header params)) :
    LiveCompletionRun (do
      let (header, params) ← newBlock types
      emitTerm (.br header arguments)
      setCur (some header)
      tail header params) :=
  complete_header_live types arguments fun header params env before result after run openBefore shapedBefore _ =>
    child header params env before result after run openBefore shapedBefore

end Goose.Lower.Validation

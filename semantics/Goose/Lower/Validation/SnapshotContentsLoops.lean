import Goose.Lower.Validation.SnapshotContentsBuilder
import Goose.Lower.Validation.SnapshotContentsSourceLeavesActions
import Goose.Lower.GeneratedTargetFramesLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem snapshot_loopBody {le : LEnv} {first : ValueId} {before : LS}
    (trace : SnapshotSourceTrace le first before before) (generated : GeneratedBuilderState before)
    (fresh : first ≤ before.vals.size)
    (condition : ValueId) (header : BlockId) (headerParams : List (ValueId × VTy))
    (context : Nat → BlockId → LoopCtx)
    (headerAt : ∃ block, before.blocks[header]? = some block ∧ block.params = headerParams)
    (makeFrames : ∀ depth exit state headBlock exitBlock,
      state.blocks[header]? = some headBlock → headBlock.params = headerParams →
      state.blocks[exit]? = some exitBlock → exitBlock.params = [] →
      LoopBuilderFrames (some (context depth exit)) state)
    (body : Nat → BlockId → B ValueId) (back : B Unit)
    (bodyChecked : ∀ depth exit, SnapshotSourceAction le (some (context depth exit)) (body depth exit))
    (backChecked : ∀ depth exit state, SnapshotSourceTrace le first state state →
      GeneratedBuilderState state → LoopBuilderFrames (some (context depth exit)) state →
      SnapshotSourceTrace le first (back le state).2 (back le state).2 ∧
        GeneratedBuilderState (back le state).2)
    (backAdvance : AdvB back) :
    SnapshotSourceTrace le first (Goose.Lower.loopBody condition body back le before).2
      (Goose.Lower.loopBody condition body back le before).2 ∧
      GeneratedBuilderState (Goose.Lower.loopBody condition body back le before).2 := by
  generalize run : Goose.Lower.loopBody condition body back le before = result
  obtain ⟨resultValue, after⟩ := result
  dsimp only
  unfold Goose.Lower.loopBody at run
  simp only [bind_eq] at run
  obtain ⟨saved, observed, savedRun, ⟨bodyBlock, exit⟩, forked, forkRun,
    _, selected, selectRun, value, evaluated, bodyRun, _, closed, backRun, resumeRun⟩ := run
  rw [get_apply] at savedRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj savedRun
  have forkTrace := trace.fork generated forkRun
  have forkGenerated := generated.fork condition forkRun
  have selectedTrace := forkTrace.setCur_full selectRun
  have ids := fork_ids forkRun
  have selectedBound : ∀ block, some bodyBlock = some block → block < forked.blocks.size := by
    intro block same
    cases Option.some.inj same
    have row := (fork_emptyRows forkRun).1
    obtain ⟨actual, located, _⟩ := row
    exact (Array.getElem?_eq_some_iff.mp located).1
  have selectedGenerated := forkGenerated.setCur _ selectedBound selectRun
  have forkExt := (advB_fork condition le before _ _ forkRun).ext
  have selectedExt : forked.Ext selected := by
    rw [setCur_run] at selectRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj selectRun
    exact .refl _
  have headerSelected : ∃ block, selected.blocks[header]? = some block ∧ block.params = headerParams := by
    obtain ⟨block, row, params⟩ := headerAt
    obtain ⟨forkBlock, forkRow, forkParams, _⟩ := forkExt.2 header block row
    obtain ⟨selectedBlock, selectedRow, selectedParams, _⟩ := selectedExt.2 header forkBlock forkRow
    exact ⟨selectedBlock, selectedRow, selectedParams.trans (forkParams.trans params)⟩
  have exitSelected : ∃ block, selected.blocks[exit]? = some block ∧ block.params = [] := by
    obtain ⟨block, row, params⟩ := (fork_emptyRows forkRun).2
    obtain ⟨selectedBlock, selectedRow, selectedParams, _⟩ := selectedExt.2 exit block row
    exact ⟨selectedBlock, selectedRow, selectedParams.trans params⟩
  have frames : LoopBuilderFrames (some (context before.stack.length exit)) selected := by
    obtain ⟨headBlock, headRow, headParams⟩ := headerSelected
    obtain ⟨exitBlock, exitRow, exitParams⟩ := exitSelected
    exact makeFrames _ _ _ _ _ headRow headParams exitRow exitParams
  have child := bodyChecked before.stack.length exit
  have selectedVals : selected.vals = forked.vals := by
    rw [setCur_run] at selectRun
    exact congrArg (fun pair => pair.2.vals) selectRun.symm
  have firstBound : first ≤ selected.vals.size := by
    rw [selectedVals]
    exact Nat.le_trans fresh (advB_fork condition le before _ _ forkRun).vals
  have evaluatedTrace := child.snapshots.continue child.dense child.advance child.types child.frames
    selectedTrace selectedGenerated frames firstBound bodyRun
  have evaluatedGenerated := selectedGenerated.of_runs child.dense child.targets frames.toTargets bodyRun
  have evaluatedFrames := frames.mono (child.advance le selected value evaluated bodyRun).ext
  have closedResult := backChecked before.stack.length exit evaluated evaluatedTrace evaluatedGenerated evaluatedFrames
  rw [backRun] at closedResult
  dsimp only at closedResult
  have resumedTrace := closedResult.1.setCur_full resumeRun
  have exitBound : exit < selected.blocks.size := by
    obtain ⟨block, row, _⟩ := exitSelected
    exact (Array.getElem?_eq_some_iff.mp row).1
  have bodyGrows := (child.advance le selected value evaluated bodyRun).ext.1
  have backGrows := (backAdvance le evaluated _ _ backRun).ext.1
  have resumedGenerated := closedResult.2.setCur (some exit) (by
    intro block same
    cases Option.some.inj same
    exact Nat.lt_of_lt_of_le exitBound (Nat.le_trans bodyGrows backGrows)) resumeRun
  exact ⟨resumedTrace, resumedGenerated⟩

theorem snapshot_lowerWhile {le : LEnv} {first : ValueId} {before : LS}
    (trace : SnapshotSourceTrace le first before before) (generated : GeneratedBuilderState before)
    (fresh : first ≤ before.vals.size) (header : BlockId)
    (headerAt : ∃ block, before.blocks[header]? = some block ∧ block.params = [])
    (condition : B ValueId) (body : Nat → BlockId → B ValueId)
    (conditionChecked : SnapshotSourceAction le none condition)
    (bodyChecked : ∀ depth exit,
      SnapshotSourceAction le (some ⟨depth, exit, .jump header⟩) (body depth exit)) :
    SnapshotSourceTrace le first (Goose.Lower.lowerWhile header condition body le before).2
      (Goose.Lower.lowerWhile header condition body le before).2 ∧
      GeneratedBuilderState (Goose.Lower.lowerWhile header condition body le before).2 := by
  generalize run : Goose.Lower.lowerWhile header condition body le before = result
  obtain ⟨resultValue, after⟩ := result
  dsimp only
  unfold Goose.Lower.lowerWhile at run
  obtain ⟨value, evaluated, conditionRun, bodyRun⟩ := bind_eq.mp run
  have evaluatedTrace := conditionChecked.snapshots.continue conditionChecked.dense
    conditionChecked.advance conditionChecked.types conditionChecked.frames trace generated trivial fresh conditionRun
  have evaluatedGenerated := generated.of_runs conditionChecked.dense conditionChecked.targets trivial conditionRun
  have evaluatedFresh := Nat.le_trans fresh (conditionChecked.advance le before value evaluated conditionRun).vals
  have evaluatedHeader : ∃ block, evaluated.blocks[header]? = some block ∧ block.params = [] := by
    obtain ⟨block, row, params⟩ := headerAt
    obtain ⟨next, located, equal, _⟩ := (conditionChecked.advance le before value evaluated conditionRun).ext.2 header block row
    exact ⟨next, located, equal.trans params⟩
  cases current : evaluated.cur with
  | none =>
    rw [whenLive_none _ _ _ current] at bodyRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj bodyRun
    exact ⟨evaluatedTrace, evaluatedGenerated⟩
  | some block =>
    rw [whenLive_some _ _ _ current] at bodyRun
    have output := snapshot_loopBody evaluatedTrace evaluatedGenerated evaluatedFresh value header []
      (fun depth exit => ⟨depth, exit, .jump header⟩) evaluatedHeader
      (fun _ _ _ _ _ headRow headParams exitRow exitParams =>
        loopBuilderFrames_jump exitRow exitParams headRow headParams)
      body (Goose.Lower.emitTerm (.br header [])) bodyChecked
      (fun depth exit state trace generated frames => by
        have headerTarget : LoopBuilderFrameTarget (some ⟨depth, exit, .jump header⟩) header := Or.inr rfl
        have resultTrace := trace.emitTerm_loop generated frames
          (fun target member => by
            have same : target = header := by simpa [Term.successors] using member
            subst target
            exact headerTarget) (show Goose.Lower.emitTerm (.br header []) le state = _ from rfl)
        refine ⟨resultTrace, generated.emitTerm (.br header []) ?_ rfl⟩
        intro destination member
        have same : destination = header := by simpa [Term.successors] using member
        subst destination
        exact frames.targetBound headerTarget)
      (advB_emitTerm _)
    rw [bodyRun] at output
    exact output

theorem snapshot_rangeBack {le : LEnv} {first : ValueId} {before : LS}
    (trace : SnapshotSourceTrace le first before before) (generated : GeneratedBuilderState before)
    (hint : IntTy) (counter header depth exit : Nat)
    (frames : LoopBuilderFrames (some ⟨depth, exit, .next header hint counter⟩) before) :
    SnapshotSourceTrace le first (Goose.Lower.rangeBack hint counter header le before).2
      (Goose.Lower.rangeBack hint counter header le before).2 ∧
      GeneratedBuilderState (Goose.Lower.rangeBack hint counter header le before).2 := by
  cases current : before.cur with
  | none =>
    have same : (Goose.Lower.rangeBack hint counter header le before).2 = before := by
      simp only [Goose.Lower.rangeBack, bind_run, isLive_none current, Bool.false_eq_true, reduceIte, pure_run]
    rw [same]
    exact ⟨trace, generated⟩
  | some block =>
    let emitted := Goose.Lower.emitDef (.next hint counter) le before
    have emittedTrace := trace.emitDef generated (show Goose.Lower.emitDef (.next hint counter) le before = emitted from rfl)
      (by intros; intro impossible; cases impossible)
    have emittedGenerated : GeneratedBuilderState emitted.2 := generated.emitDef (.next hint counter) rfl
    have emittedFrames := frames.mono (advB_emitDef (.next hint counter) le before emitted.1 emitted.2 rfl).ext
    have headerTarget : LoopBuilderFrameTarget (some ⟨depth, exit, .next header hint counter⟩) header := Or.inr rfl
    have closedTrace := emittedTrace.emitTerm_loop emittedGenerated emittedFrames
      (term := .br header [emitted.1])
      (fun target member => by
        have same : target = header := by simpa [Term.successors] using member
        subst target
        exact headerTarget) rfl
    have closedGenerated := emittedGenerated.emitTerm (.br header [emitted.1]) (by
      intro target member
      have same : target = header := by simpa [Term.successors] using member
      subst target
      exact emittedFrames.targetBound headerTarget) (env := le) rfl
    have active : Goose.Lower.isLive le before = (true, before) := by
      simp [Goose.Lower.isLive, Goose.Lower.curBlock, bind_run, current, pure_run]
    have same : (Goose.Lower.rangeBack hint counter header le before).2 =
        (Goose.Lower.emitTerm (.br header [emitted.1]) le emitted.2).2 := by
      simp only [Goose.Lower.rangeBack, bind_run, active, reduceIte]
      rfl
    rw [same]
    exact ⟨closedTrace, closedGenerated⟩

theorem snapshot_lowerRange {le : LEnv} {first : ValueId} {before : LS}
    (trace : SnapshotSourceTrace le first before before) (generated : GeneratedBuilderState before)
    (fresh : first ≤ before.vals.size) (hint : IntTy) (counter upper header : ValueId)
    (headerAt : ∃ block, before.blocks[header]? = some block ∧
      block.params = [(counter, .data (.int hint))])
    (body : Nat → BlockId → B ValueId)
    (bodyChecked : ∀ depth exit,
      SnapshotSourceAction le (some ⟨depth, exit, .next header hint counter⟩) (body depth exit)) :
    SnapshotSourceTrace le first (Goose.Lower.lowerRange hint counter upper header body le before).2
      (Goose.Lower.lowerRange hint counter upper header body le before).2 ∧
      GeneratedBuilderState (Goose.Lower.lowerRange hint counter upper header body le before).2 := by
  let compared := Goose.Lower.emitDef (.cmp .lt hint counter upper) le before
  have comparedTrace := trace.emitDef generated
    (show Goose.Lower.emitDef (.cmp .lt hint counter upper) le before = compared from rfl)
    (by intros; intro impossible; cases impossible)
  have comparedGenerated : GeneratedBuilderState compared.2 := generated.emitDef (.cmp .lt hint counter upper) rfl
  have comparedFresh := Nat.le_trans fresh (advB_emitDef (.cmp .lt hint counter upper) le before _ _ rfl).vals
  have comparedHeader : ∃ block, compared.2.blocks[header]? = some block ∧
      block.params = [(counter, .data (.int hint))] := by
    obtain ⟨block, row, params⟩ := headerAt
    obtain ⟨next, located, equal, _⟩ := (advB_emitDef (.cmp .lt hint counter upper) le before _ _ rfl).ext.2 header block row
    exact ⟨next, located, equal.trans params⟩
  exact snapshot_loopBody comparedTrace comparedGenerated comparedFresh compared.1 header
    [(counter, .data (.int hint))] (fun depth exit => ⟨depth, exit, .next header hint counter⟩) comparedHeader
    (fun _ _ _ _ _ headRow headParams exitRow exitParams =>
      loopBuilderFrames_next exitRow exitParams headRow headParams)
    body (Goose.Lower.rangeBack hint counter header) bodyChecked
    (fun depth exit state trace generated frames => snapshot_rangeBack trace generated hint counter header depth exit frames)
    (advB_rangeBack _ _ _)

theorem snapshot_lowerEach {le : LEnv} {first : ValueId} {before : LS}
    (trace : SnapshotSourceTrace le first before before) (generated : GeneratedBuilderState before)
    (fresh : first ≤ before.vals.size) (regrow : Bool) (owner : Option ValueId)
    (sampled header counter : ValueId)
    (headerAt : ∃ block, before.blocks[header]? = some block ∧
      block.params = [(counter, .data (.int .i64))])
    (body : Nat → BlockId → B ValueId)
    (bodyChecked : ∀ depth exit,
      SnapshotSourceAction le (some ⟨depth, exit, .next header .i64 counter⟩) (body depth exit)) :
    SnapshotSourceTrace le first (Goose.Lower.lowerEach regrow owner sampled header counter body le before).2
      (Goose.Lower.lowerEach regrow owner sampled header counter body le before).2 ∧
      GeneratedBuilderState (Goose.Lower.lowerEach regrow owner sampled header counter body le before).2 := by
  let length := Goose.Lower.eachLen regrow owner sampled le before
  have lengthTrace : SnapshotSourceTrace le first length.2 length.2 := by
    cases regrow
    · exact trace
    · exact trace.emitDef generated (op := .arrayLen (owner.getD 0)) rfl
        (by intros; intro impossible; cases impossible)
  have lengthGenerated : GeneratedBuilderState length.2 := generated.eachLen (env := le) regrow owner sampled rfl
  have lengthFresh := Nat.le_trans fresh (advB_eachLen regrow owner sampled le before _ _ rfl).vals
  have lengthHeader : ∃ block, length.2.blocks[header]? = some block ∧
      block.params = [(counter, .data (.int .i64))] := by
    obtain ⟨block, row, params⟩ := headerAt
    obtain ⟨next, located, equal, _⟩ := (advB_eachLen regrow owner sampled le before _ _ rfl).ext.2 header block row
    exact ⟨next, located, equal.trans params⟩
  exact snapshot_lowerRange lengthTrace lengthGenerated lengthFresh .i64 counter length.1 header lengthHeader body bodyChecked

end Goose.Lower.Validation

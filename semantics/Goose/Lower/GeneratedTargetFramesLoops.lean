import Goose.Lower.GeneratedTargetFramesControl

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Lower.Validation

theorem generatedTargetFrame_rangeBackFresh (loop : Option LoopCtx) (hint : IntTy)
    (counter header : ValueId) {base before after : LS} {env : LEnv} {result : Unit}
    (headerFresh : base.blocks.size ≤ header) (frames : LoopBuilderFrames loop base)
    (oldFrames : TermEdgesFramed loop base before) (baseBefore : base.Ext before)
    (run : rangeBack hint counter header env before = (result, after)) :
    TermEdgesFramed loop base after ∧ before.Ext after := by
  unfold rangeBack at run
  obtain ⟨live, middle, tested, tail⟩ := bind_eq.mp run
  have same : middle = before := by
    have stable : (isLive env before).2 = before := rfl
    rw [tested] at stable
    exact stable
  subst middle
  cases live with
  | false =>
      simp only [Bool.false_eq_true, ite_false, pure_run] at tail
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj tail
      exact ⟨oldFrames, .refl _⟩
  | true =>
      simp only [ite_true, bind_eq] at tail
      obtain ⟨value, middle, emitted, branched⟩ := tail
      have emittedChecked := generatedTargetFrame_emitDef loop (.next hint counter)
        base env before value middle baseBefore frames oldFrames emitted
      have branchFrames := emittedChecked.1.emitTermAt branched (by
        intro target successor targetBound
        simp only [Term.successors, List.mem_singleton] at successor
        subst target
        exact False.elim (Nat.not_lt_of_ge headerFresh targetBound))
      have branchExt := (advB_emitTerm (.br header [value]) env middle () after branched).ext
      exact ⟨branchFrames, emittedChecked.2.trans branchExt⟩

theorem generatedTargetFrame_loopBodyFresh (loop : Option LoopCtx) (header : BlockId)
    (context : Nat → BlockId → LoopCtx) (headerParams : List (ValueId × VTy))
    {base current after : LS} {env : LEnv} {result : Unit}
    {body : Nat → BlockId → B ValueId} {back : B Unit} (condition : ValueId)
    (bodyChecked : ∀ depth exit, GeneratedTargetFrameRun (some (context depth exit)) (body depth exit))
    (makeFrames : ∀ depth exit state headBlock exitBlock,
      state.blocks[header]? = some headBlock → headBlock.params = headerParams →
      state.blocks[exit]? = some exitBlock → exitBlock.params = [] →
      LoopBuilderFrames (some (context depth exit)) state)
    (targetCases : ∀ depth exit target,
      LoopBuilderFrameTarget (some (context depth exit)) target → target = header ∨ target = exit)
    (headerFresh : base.blocks.size ≤ header)
    (backChecked : ∀ {env before result after}, base.Ext before →
      TermEdgesFramed loop base before → back env before = (result, after) →
      TermEdgesFramed loop base after ∧ before.Ext after)
    (baseCurrent : base.Ext current) (outerFrames : LoopBuilderFrames loop base)
    (oldFrames : TermEdgesFramed loop base current)
    (headerAt : ∃ block, current.blocks[header]? = some block ∧ block.params = headerParams)
    (run : loopBody condition body back env current = (result, after)) :
    TermEdgesFramed loop base after ∧ current.Ext after := by
  unfold loopBody at run
  simp only [bind_eq] at run
  obtain ⟨saved, first, savedRun, ⟨bodyBlock, exit⟩, forked, forkRun,
    ignored, selected, selectedRun, value, bodyEnd, bodyRun,
    ignored', backEnd, backRun, selectExit⟩ := run
  rw [get_apply] at savedRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj savedRun
  have forkedChecked := generatedTargetFrame_fork loop condition base env current _ forked
    baseCurrent outerFrames oldFrames
    forkRun
  have forkExt := (advB_fork condition env current _ forked forkRun).ext
  have selectedChecked := generatedTargetFrame_setCur loop (some bodyBlock) base env forked () selected
    (baseCurrent.trans forkExt) outerFrames forkedChecked.1 selectedRun
  have selectedExt := selectedChecked.2
  have rootSelected := baseCurrent.trans (forkExt.trans selectedExt)
  have headerAtFork : ∃ block, forked.blocks[header]? = some block ∧ block.params = headerParams := by
    rcases headerAt with ⟨block, row, params⟩
    rcases forkExt.2 header block row with ⟨block', row', params', _⟩
    exact ⟨block', row', params'.trans params⟩
  have headerAtSelected : ∃ block, selected.blocks[header]? = some block ∧ block.params = headerParams := by
    rcases headerAtFork with ⟨block, row, params⟩
    have same := setCur_blocks selectedRun
    exact ⟨block, by rw [same]; exact row, params⟩
  have forkRows := fork_emptyRows forkRun
  have exitAtFork : ∃ block, forked.blocks[exit]? = some block ∧ block.params = [] := by
    rcases forkRows.2 with ⟨block, row, params⟩
    exact ⟨block, row, params⟩
  have exitAtSelected : ∃ block, selected.blocks[exit]? = some block ∧ block.params = [] := by
    rcases exitAtFork with ⟨block, row, params⟩
    have same := setCur_blocks selectedRun
    exact ⟨block, by rw [same]; exact row, params⟩
  have framesSelected : LoopBuilderFrames (some (context current.stack.length exit)) selected := by
    rcases headerAtSelected with ⟨headBlock, headAt, headParams⟩
    rcases exitAtSelected with ⟨exitBlock, exitAt, exitParams⟩
    exact makeFrames current.stack.length exit selected headBlock exitBlock
      headAt headParams exitAt exitParams
  have bodyResult := bodyChecked current.stack.length exit selected env selected value bodyEnd
    (.refl _) framesSelected (TermEdgesFramed.refl _ _) bodyRun
  have forkFresh := generatedTargetFrame_forkFresh baseCurrent forkRun
  have backResult := TermEdgesFramed.rebase selectedChecked.1 bodyResult.1
    rootSelected (fun target framed => by
      rcases targetCases current.stack.length exit target framed with isHeader | isExit
      · subst target
        exact Or.inr headerFresh
      · subst target
        exact Or.inr forkFresh.2)
  have backCheckedResult := backChecked (rootSelected.trans bodyResult.2) backResult backRun
  have finalChecked := generatedTargetFrame_setCur loop (some exit) base env backEnd result after
    ((rootSelected.trans bodyResult.2).trans backCheckedResult.2) outerFrames backCheckedResult.1 selectExit
  exact ⟨finalChecked.1, (((forkExt.trans selectedExt).trans bodyResult.2).trans backCheckedResult.2).trans finalChecked.2⟩

theorem generatedTargetFrame_lowerRangeFresh (loop : Option LoopCtx) (hint : IntTy)
    (counter bound header : ValueId) {body : Nat → BlockId → B ValueId}
    (bodyChecked : ∀ depth exit,
      GeneratedTargetFrameRun (some ⟨depth, exit, .next header hint counter⟩) (body depth exit))
    {base current after : LS} {env : LEnv} {result : Unit}
    (baseCurrent : base.Ext current) (outerFrames : LoopBuilderFrames loop base)
    (oldFrames : TermEdgesFramed loop base current)
    (headerFresh : base.blocks.size ≤ header)
    (headerAt : ∃ block, current.blocks[header]? = some block ∧
      block.params = [(counter, .data (.int hint))])
    (run : lowerRange hint counter bound header body env current = (result, after)) :
    TermEdgesFramed loop base after ∧ current.Ext after := by
  unfold lowerRange at run
  obtain ⟨condition, middle, compareRun, tail⟩ := bind_eq.mp run
  have compareChecked := generatedTargetFrame_emitDef loop (.cmp .lt hint counter bound)
    base env current condition middle baseCurrent outerFrames oldFrames compareRun
  have headerAtMiddle : ∃ block, middle.blocks[header]? = some block ∧
      block.params = [(counter, .data (.int hint))] := by
    rcases headerAt with ⟨block, row, params⟩
    rcases compareChecked.2.2 header block row with ⟨block', row', params', _⟩
    exact ⟨block', row', params'.trans params⟩
  have bodyFrames : ∀ depth exit state headBlock exitBlock,
      state.blocks[header]? = some headBlock → headBlock.params = [(counter, .data (.int hint))] →
      state.blocks[exit]? = some exitBlock → exitBlock.params = [] →
      LoopBuilderFrames (some ⟨depth, exit, .next header hint counter⟩) state := by
    intro depth exit state headBlock exitBlock headAt headParams exitAt exitParams
    exact loopBuilderFrames_next exitAt exitParams headAt headParams
  have loopResult := generatedTargetFrame_loopBodyFresh loop header
    (fun depth exit => ⟨depth, exit, .next header hint counter⟩)
    [(counter, .data (.int hint))] condition bodyChecked
    bodyFrames
    (by
      intro depth exit target framed
      simp only [LoopBuilderFrameTarget] at framed
      rcases framed with isExit | isHeader
      · exact Or.inr isExit
      · exact Or.inl isHeader)
    headerFresh
    (by
      intro env before result after baseBefore backFrames backRun
      exact generatedTargetFrame_rangeBackFresh loop hint counter header headerFresh outerFrames
        backFrames baseBefore backRun)
    (baseCurrent := baseCurrent.trans compareChecked.2)
    outerFrames compareChecked.1 headerAtMiddle tail
  exact ⟨loopResult.1, compareChecked.2.trans loopResult.2⟩

theorem generatedTargetFrame_lowerEachFresh (loop : Option LoopCtx) (regrow : Bool)
    (owner : Option ValueId) (sampled header counter : ValueId)
    {body : Nat → BlockId → B ValueId}
    (bodyChecked : ∀ depth exit,
      GeneratedTargetFrameRun (some ⟨depth, exit, .next header .i64 counter⟩) (body depth exit))
    {base current after : LS} {env : LEnv} {result : Unit}
    (baseCurrent : base.Ext current) (outerFrames : LoopBuilderFrames loop base)
    (oldFrames : TermEdgesFramed loop base current)
    (headerFresh : base.blocks.size ≤ header)
    (headerAt : ∃ block, current.blocks[header]? = some block ∧
      block.params = [(counter, .data (.int .i64))])
    (run : lowerEach regrow owner sampled header counter body env current = (result, after)) :
    TermEdgesFramed loop base after ∧ current.Ext after := by
  unfold lowerEach at run
  simp only [bind_eq] at run
  obtain ⟨length, measured, measuredRun, condition, compared, compareRun, bodyRun⟩ := run
  have measuredChecked := generatedTargetFrame_eachLen loop regrow owner sampled
    base env current length measured baseCurrent outerFrames oldFrames measuredRun
  have headerAtMeasured : ∃ block, measured.blocks[header]? = some block ∧
      block.params = [(counter, .data (.int .i64))] := by
    rcases headerAt with ⟨block, row, params⟩
    rcases measuredChecked.2.2 header block row with ⟨block', row', params', _⟩
    exact ⟨block', row', params'.trans params⟩
  have compareChecked := generatedTargetFrame_emitDef loop (.cmp .lt .i64 counter length)
    base env measured condition compared (baseCurrent.trans measuredChecked.2)
    outerFrames measuredChecked.1 compareRun
  have headerAtCompared : ∃ block, compared.blocks[header]? = some block ∧
      block.params = [(counter, .data (.int .i64))] := by
    rcases headerAtMeasured with ⟨block, row, params⟩
    rcases compareChecked.2.2 header block row with ⟨block', row', params', _⟩
    exact ⟨block', row', params'.trans params⟩
  have bodyFrames : ∀ depth exit state headBlock exitBlock,
      state.blocks[header]? = some headBlock → headBlock.params = [(counter, .data (.int .i64))] →
      state.blocks[exit]? = some exitBlock → exitBlock.params = [] →
      LoopBuilderFrames (some ⟨depth, exit, .next header .i64 counter⟩) state := by
    intro depth exit state headBlock exitBlock headAt headParams exitAt exitParams
    exact loopBuilderFrames_next exitAt exitParams headAt headParams
  have loopResult := generatedTargetFrame_loopBodyFresh loop header
    (fun depth exit => ⟨depth, exit, .next header .i64 counter⟩)
    [(counter, .data (.int .i64))] condition bodyChecked bodyFrames
    (by
      intro depth exit target framed
      simp only [LoopBuilderFrameTarget] at framed
      rcases framed with isExit | isHeader
      · exact Or.inr isExit
      · exact Or.inl isHeader)
    headerFresh
    (by
      intro innerEnv before result after baseBefore backFrames backRun
      exact generatedTargetFrame_rangeBackFresh loop .i64 counter header headerFresh
        outerFrames backFrames baseBefore backRun)
    (baseCurrent := (baseCurrent.trans measuredChecked.2).trans compareChecked.2)
    outerFrames compareChecked.1 headerAtCompared bodyRun
  exact ⟨loopResult.1, ((measuredChecked.2.trans compareChecked.2).trans loopResult.2)⟩

theorem generatedTargetFrame_lowerWhileFresh (loop : Option LoopCtx) (header : BlockId)
    {condition : B ValueId} {body : Nat → BlockId → B ValueId}
    (conditionChecked : GeneratedTargetFrameRun none condition)
    (bodyChecked : ∀ depth exit,
      GeneratedTargetFrameRun (some ⟨depth, exit, .jump header⟩) (body depth exit))
    {base current after : LS} {env : LEnv} {result : Unit}
    (baseCurrent : base.Ext current) (outerFrames : LoopBuilderFrames loop base)
    (oldFrames : TermEdgesFramed loop base current)
    (headerFresh : base.blocks.size ≤ header)
    (headerAt : ∃ block, current.blocks[header]? = some block ∧ block.params = [])
    (run : lowerWhile header condition body env current = (result, after)) :
    TermEdgesFramed loop base after ∧ current.Ext after := by
  unfold lowerWhile at run
  obtain ⟨value, middle, conditionRun, tail⟩ := bind_eq.mp run
  have conditionResult := conditionChecked.withLoop (outer := loop)
    base env current value middle baseCurrent outerFrames oldFrames conditionRun
  have headerAtMiddle : ∃ block, middle.blocks[header]? = some block ∧ block.params = [] := by
    rcases headerAt with ⟨block, row, params⟩
    rcases conditionResult.2.2 header block row with ⟨block', row', params', _⟩
    exact ⟨block', row', params'.trans params⟩
  cases currentMiddle : middle.cur with
  | none =>
      rw [whenLive_none _ _ env currentMiddle] at tail
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj tail
      exact ⟨conditionResult.1, conditionResult.2⟩
  | some block =>
      rw [whenLive_some _ _ env currentMiddle] at tail
      have bodyFrames : ∀ depth exit state headBlock exitBlock,
          state.blocks[header]? = some headBlock → headBlock.params = [] →
          state.blocks[exit]? = some exitBlock → exitBlock.params = [] →
          LoopBuilderFrames (some ⟨depth, exit, .jump header⟩) state := by
        intro depth exit state headBlock exitBlock headAt headParams exitAt exitParams
        exact loopBuilderFrames_jump exitAt exitParams headAt headParams
      have backChecked : ∀ {env before result after}, base.Ext before →
          TermEdgesFramed loop base before → emitTerm (.br header []) env before = (result, after) →
          TermEdgesFramed loop base after ∧ before.Ext after := by
        intro innerEnv before result after beforeRoot terms backRun
        have afterFrames := terms.emitTermAt backRun (by
          intro target successor targetBound
          simp only [Term.successors, List.mem_singleton] at successor
          subst target
          exact False.elim (Nat.not_lt_of_ge headerFresh targetBound))
        exact ⟨afterFrames, (advB_emitTerm (.br header []) innerEnv before result after backRun).ext⟩
      have bodyResult := generatedTargetFrame_loopBodyFresh loop header
        (fun depth exit => ⟨depth, exit, .jump header⟩) [] value bodyChecked
        bodyFrames
        (by
          intro depth exit target framed
          simp only [LoopBuilderFrameTarget] at framed
          rcases framed with isExit | isHeader
          · exact Or.inr isExit
          · exact Or.inl isHeader)
        headerFresh backChecked
        (baseCurrent := baseCurrent.trans conditionResult.2)
        outerFrames conditionResult.1 headerAtMiddle tail
      exact ⟨bodyResult.1, conditionResult.2.trans bodyResult.2⟩

theorem generatedTargetFrame_header0 (loop : Option LoopCtx) {tail : BlockId → B Unit}
    (tailChecked : ∀ header {base : LS} {env : LEnv} {current after : LS} {result : Unit},
      base.Ext current → LoopBuilderFrames loop base → TermEdgesFramed loop base current →
      base.blocks.size ≤ header →
      (∃ block, current.blocks[header]? = some block ∧ block.params = []) →
      tail header env current = (result, after) →
      TermEdgesFramed loop base after ∧ current.Ext after) :
    GeneratedTargetFrameRun loop (do
      let (header, _) ← newBlock []
      emitTerm (.br header [])
      setCur (some header)
      tail header) := by
  intro base env current result after baseCurrent frames oldFrames run
  simp only [bind_eq] at run
  obtain ⟨⟨header, ids⟩, allocated, allocateRun, ignored, branched, branchRun,
    ignored', selected, selectRun, tailRun⟩ := run
  have allocatedChecked := generatedTargetFrame_newBlock loop [] base env current
    (header, ids) allocated baseCurrent frames oldFrames allocateRun
  have headerFresh := newBlock_fresh baseCurrent allocateRun
  have branchFrames := allocatedChecked.1.emitTermAt branchRun (by
    intro target successor targetBound
    simp only [Term.successors, List.mem_singleton] at successor
    subst target
    exact False.elim (Nat.not_lt_of_ge headerFresh targetBound))
  have branchExt := (advB_emitTerm (.br header []) env allocated () branched branchRun).ext
  have selectedChecked := generatedTargetFrame_setCur loop (some header) base env branched () selected
    ((baseCurrent.trans allocatedChecked.2).trans branchExt) frames branchFrames selectRun
  have headerAtAllocated : ∃ block, allocated.blocks[header]? = some block ∧ block.params = [] := by
    obtain ⟨block, row, params⟩ := newBlock_params allocateRun
    exact ⟨block, by simpa using row, by simpa using params⟩
  have headerAtBranched : ∃ block, branched.blocks[header]? = some block ∧ block.params = [] := by
    obtain ⟨block, row, params⟩ := headerAtAllocated
    rcases branchExt.2 header block row with ⟨block', row', params', _⟩
    exact ⟨block', row', params'.trans params⟩
  have headerAtSelected : ∃ block, selected.blocks[header]? = some block ∧ block.params = [] := by
    obtain ⟨block, row, params⟩ := headerAtBranched
    have same := setCur_blocks selectRun
    exact ⟨block, by rw [same]; exact row, params⟩
  have tailResult := tailChecked header (base := base) (env := env) (current := selected)
    (after := after) (result := result)
    (((baseCurrent.trans allocatedChecked.2).trans branchExt).trans selectedChecked.2)
    frames selectedChecked.1 headerFresh headerAtSelected tailRun
  exact ⟨tailResult.1,
    (((allocatedChecked.2.trans branchExt).trans selectedChecked.2).trans tailResult.2)⟩

theorem generatedTargetFrame_header1 (loop : Option LoopCtx) (hint : IntTy) (initial : ValueId)
    {tail : BlockId → ValueId → B Unit}
    (tailChecked : ∀ header counter {base : LS} {env : LEnv} {current after : LS} {result : Unit},
      base.Ext current → LoopBuilderFrames loop base → TermEdgesFramed loop base current →
      base.blocks.size ≤ header →
      (∃ block, current.blocks[header]? = some block ∧
        block.params = [(counter, .data (.int hint))]) →
      tail header counter env current = (result, after) →
      TermEdgesFramed loop base after ∧ current.Ext after) :
    GeneratedTargetFrameRun loop (do
      let (header, ids) ← newBlock [.data (.int hint)]
      let counter := ids.headD 0
      emitTerm (.br header [initial])
      setCur (some header)
      tail header counter) := by
  intro base env current result after baseCurrent frames oldFrames run
  simp only [bind_eq] at run
  obtain ⟨⟨header, ids⟩, allocated, allocateRun, ignored, branched, branchRun,
    ignored', selected, selectRun, tailRun⟩ := run
  let counter := ids.headD 0
  have allocatedChecked := generatedTargetFrame_newBlock loop [.data (.int hint)] base env current
    (header, ids) allocated baseCurrent frames oldFrames allocateRun
  have headerFresh := newBlock_fresh baseCurrent allocateRun
  have branchFrames := allocatedChecked.1.emitTermAt branchRun (by
    intro target successor targetBound
    simp only [Term.successors, List.mem_singleton] at successor
    subst target
    exact False.elim (Nat.not_lt_of_ge headerFresh targetBound))
  have branchExt := (advB_emitTerm (.br header [initial]) env allocated () branched branchRun).ext
  have selectedChecked := generatedTargetFrame_setCur loop (some header) base env branched () selected
    ((baseCurrent.trans allocatedChecked.2).trans branchExt) frames branchFrames selectRun
  have idsExact : ids = [current.vals.size] := by
    rw [newBlock_run_general] at allocateRun
    have resultEq := (Prod.mk.inj allocateRun).1
    simpa [paramIds] using (congrArg Prod.snd resultEq).symm
  have counterExact : counter = current.vals.size := by
    dsimp [counter]
    rw [idsExact]
    rfl
  have headerAtAllocated : ∃ block, allocated.blocks[header]? = some block ∧
      block.params = [(counter, .data (.int hint))] := by
    obtain ⟨block, row, shape⟩ := newBlock_params allocateRun
    refine ⟨block, by simpa using row, ?_⟩
    simpa [idsExact, counterExact] using shape
  have headerAtBranched : ∃ block, branched.blocks[header]? = some block ∧
      block.params = [(counter, .data (.int hint))] := by
    obtain ⟨block, row, params⟩ := headerAtAllocated
    rcases branchExt.2 header block row with ⟨block', row', params', _⟩
    exact ⟨block', row', params'.trans params⟩
  have headerAtSelected : ∃ block, selected.blocks[header]? = some block ∧
      block.params = [(counter, .data (.int hint))] := by
    obtain ⟨block, row, params⟩ := headerAtBranched
    have same := setCur_blocks selectRun
    exact ⟨block, by rw [same]; exact row, params⟩
  have tailResult := tailChecked header counter (base := base) (env := env) (current := selected)
    (after := after) (result := result)
    (((baseCurrent.trans allocatedChecked.2).trans branchExt).trans selectedChecked.2)
    frames selectedChecked.1 headerFresh headerAtSelected tailRun
  exact ⟨tailResult.1,
    (((allocatedChecked.2.trans branchExt).trans selectedChecked.2).trans tailResult.2)⟩

end Goose.Lower

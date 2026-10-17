import Goose.Lower.Validation.PermissionInstructionControlScopes

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem NewPermissionInstructions.loopBody
    {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat}
    {outer : Option LoopCtx} {header : BlockId} {condition : ValueId} {body : Goose.Core.Block}
    {source current after : LS}
    (initialPermission : NewPermissionInstructions module func le first source current)
    (run : Goose.Lower.loopBody condition
      (fun depth exit => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body)
      (Goose.Lower.emitTerm (.br header [])) le current = ((), after))
    (firstBound : first ≤ current.vals.size)
    (generated : GeneratedBuilderState current) (frames : LoopBuilderFrames outer current)
    (headerAt : ∃ block, current.blocks[header]? = some block ∧ block.params = [])
    (bodyNew : ∀ {depth exit input output value},
      lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body le input = (value, output) →
      GeneratedBuilderState input → LoopBuilderFrames (some ⟨depth, exit, .jump header⟩) input →
      first ≤ input.vals.size →
      NewPermissionInstructions module func le first input output) :
    NewPermissionInstructions module func le first source after := by
  unfold Goose.Lower.loopBody at run
  simp only [bind_eq] at run
  obtain ⟨saved, firstState, savedRun, ⟨bodyBlock, exit⟩, forked, forkRun,
    ignored, selected, selectedRun, value, bodyEnd, bodyRun,
    ignored', backEnd, backRun, selectExit⟩ := run
  rw [get_apply] at savedRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj savedRun
  have forkNew := NewPermissionInstructions.fork
    (module := module) (func := func) (le := le) (first := first) forkRun
  have forkedGenerated := generated.fork condition forkRun
  have forkAdvance := advB_fork condition le current _ forked forkRun
  have forkFloor := Nat.le_trans firstBound forkAdvance.vals
  have headerAtFork : ∃ block, forked.blocks[header]? = some block ∧ block.params = [] := by
    rcases headerAt with ⟨block, row, params⟩
    rcases forkAdvance.ext.2 header block row with ⟨block', row', params', _⟩
    exact ⟨block', row', params'.trans params⟩
  have forkIds := fork_ids forkRun
  rcases Prod.mk.inj forkIds.1 with ⟨bodyId, exitId⟩
  subst bodyBlock
  subst exit
  let loopBodyId : BlockId := current.blocks.size
  let loopExitId : BlockId := current.blocks.size + 1
  have forkedBlockCount : forked.blocks.size = current.blocks.size + 2 := forkIds.2
  have forkRows := fork_emptyRows forkRun
  let inner : Option LoopCtx := some ⟨current.stack.length, loopExitId, .jump header⟩
  have innerFrames : LoopBuilderFrames inner forked := by
    rcases headerAtFork with ⟨headerBlock, headerRow, headerParams⟩
    rcases forkRows.2 with ⟨exitBlock, exitRow, exitParams⟩
    simpa [inner, loopExitId] using
      (loopBuilderFrames_jump (depth := current.stack.length) exitRow exitParams headerRow headerParams)
  have bodyBlockBound : loopBodyId < forked.blocks.size := by
    dsimp [loopBodyId]
    rw [forkedBlockCount]
    exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
  have forkSelected := NewPermissionInstructions.append_setCur
    (NewPermissionInstructions.compose_framed initialPermission forkNew forkRun
      (dense_fork condition) (advB_fork condition) (types_fork condition)
      (generatedTargetFrame_fork outer condition) generated frames)
    selectedRun
  have selectedGenerated := forkedGenerated.setCur (some loopBodyId)
    (by intro target same; cases same; exact bodyBlockBound) selectedRun
  have selectedFrames := innerFrames.of_blocks (setCur_blocks selectedRun)
  have selectedFloor : first ≤ selected.vals.size := by
    have sameVals : selected.vals = forked.vals := by
      rw [setCur_run] at selectedRun
      rcases Prod.mk.inj selectedRun with ⟨_, rfl⟩
      rfl
    simpa [sameVals] using forkFloor
  have bodyRunNew := bodyNew bodyRun selectedGenerated selectedFrames selectedFloor
  change lowerBlock inner [] false body le selected = (value, bodyEnd) at bodyRun
  have bodyGenerated := selectedGenerated.lowerBlock inner [] false body
    selectedFrames.toTargets bodyRun
  have bodyFrames := selectedFrames.mono
    (advB_lowerBlock inner [] false body le selected value bodyEnd bodyRun).ext
  have bodyComposition := NewPermissionInstructions.compose_framed forkSelected bodyRunNew bodyRun
    (dense_lowerBlock inner [] false body) (advB_lowerBlock inner [] false body)
    (types_lowerBlock inner [] false body) (generatedTargetFrame_lowerBlock inner [] false body)
    selectedGenerated selectedFrames
  have backNew := NewPermissionInstructions.branch
    (module := module) (func := func) (le := le) (first := first) backRun
  have backFrames : GeneratedTargetFrameRun inner (Goose.Lower.emitTerm (.br header [])) :=
    generatedTargetFrame_emitTerm inner (.br header []) (by
      intro base target member bound
      simp only [Term.successors, List.mem_singleton] at member
      subst target
      simp [LoopBuilderFrameTarget, inner])
  have backComposition := NewPermissionInstructions.compose_framed bodyComposition backNew backRun
    (dense_emitTerm (.br header [])) (advB_emitTerm (.br header []))
    (types_emitTerm (.br header [])) backFrames bodyGenerated bodyFrames
  exact NewPermissionInstructions.append_setCur backComposition selectExit

theorem lowerWhile_newPermissionInstructions
    {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat}
    {outer : Option LoopCtx} {header : BlockId} {condition : Expr} {body : Goose.Core.Block}
    {source before after : LS}
    (initialPermission : NewPermissionInstructions module func le first source before)
    (run : Goose.Lower.lowerWhile header (lowerExpr condition)
      (fun depth exit => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body)
      le before = ((), after))
    (firstBound : first ≤ before.vals.size)
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames outer before)
    (headerAt : ∃ block, before.blocks[header]? = some block ∧ block.params = [])
    (conditionNew : ∀ {input output value}, lowerExpr condition le input = (value, output) →
      GeneratedBuilderState input → LoopBuilderFrames outer input →
      first ≤ input.vals.size →
      NewPermissionInstructions module func le first input output)
    (bodyNew : ∀ {depth exit input output value},
      lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body le input = (value, output) →
      GeneratedBuilderState input → LoopBuilderFrames (some ⟨depth, exit, .jump header⟩) input →
      first ≤ input.vals.size →
      NewPermissionInstructions module func le first input output) :
    NewPermissionInstructions module func le first source after := by
  unfold Goose.Lower.lowerWhile at run
  obtain ⟨conditionValue, conditionState, conditionRun, tailRun⟩ := bind_eq.mp run
  have conditionGenerated := generated.lowerExpr condition conditionRun
  have conditionAdvance := advB_lowerExpr condition le before conditionValue conditionState conditionRun
  have conditionFloor := Nat.le_trans firstBound conditionAdvance.vals
  have conditionPermission := conditionNew conditionRun generated frames firstBound
  have conditionFrames := frames.mono conditionAdvance.ext
  have conditionComposition := NewPermissionInstructions.compose_framed initialPermission conditionPermission
    conditionRun (dense_lowerExpr condition) (advB_lowerExpr condition)
    (types_lowerExpr condition) (generatedTargetFrame_lowerExpr outer condition)
    generated frames
  have headerAtCondition :
      ∃ block, conditionState.blocks[header]? = some block ∧ block.params = [] := by
    rcases headerAt with ⟨block, row, params⟩
    rcases conditionAdvance.ext.2 header block row with ⟨block', row', params', _⟩
    exact ⟨block', row', params'.trans params⟩
  cases live : conditionState.cur with
  | none =>
    rw [whenLive_none _ _ le live] at tailRun
    rcases Prod.mk.inj tailRun with ⟨_, stateEq⟩
    subst after
    exact conditionComposition
  | some current =>
    rw [whenLive_some _ _ le live] at tailRun
    exact NewPermissionInstructions.loopBody conditionComposition tailRun conditionFloor
      conditionGenerated conditionFrames headerAtCondition bodyNew

theorem lowerStmt_while_newPermissionInstructions
    {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat}
    {loop : Option LoopCtx} {condition : Expr} {body : Goose.Core.Block} {origin : OriginId}
    {before after : LS}
    (run : lowerStmt loop (.while condition body origin) le before = ((), after))
    (firstBound : first ≤ before.vals.size)
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before)
    (conditionNew : ∀ {input output value}, lowerExpr condition le input = (value, output) →
      GeneratedBuilderState input → LoopBuilderFrames loop input →
      first ≤ input.vals.size →
      NewPermissionInstructions module func le first input output)
    (bodyNew : ∀ {header depth exit input output value},
      lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body le input =
        (value, output) → GeneratedBuilderState input →
        LoopBuilderFrames (some ⟨depth, exit, .jump header⟩) input →
        first ≤ input.vals.size →
        NewPermissionInstructions module func le first input output) :
    NewPermissionInstructions module func le first before after := by
  change (do
    let (header, _) ← newBlock []
    Goose.Lower.emitTerm (.br header [])
    setCur (some header)
    Goose.Lower.lowerWhile header (lowerExpr condition)
      (fun depth exit => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body)) le before =
      ((), after) at run
  simp only [bind_eq] at run
  obtain ⟨⟨header, params⟩, allocated, allocationRun, _, branched, branchRun,
    _, selected, selectRun, whileRun⟩ := run
  have allocationShape := allocationRun
  rw [newBlock_run_general] at allocationShape
  obtain ⟨resultShape, _⟩ := Prod.mk.inj allocationShape
  rcases Prod.mk.inj resultShape with ⟨headerEq, paramsEq⟩
  subst header
  let header : BlockId := before.blocks.size
  have paramsEmpty : params = [] := by simpa [paramIds] using paramsEq.symm
  subst params
  have allocationNew := NewPermissionInstructions.newBlock
    (module := module) (func := func) (le := le) (first := first) allocationRun
  have allocationInsts : allocated.insts = before.insts := by
    rw [newBlock_run_general] at allocationRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj allocationRun
    simp [LS.insts, paramIds]
  have branchNew := NewPermissionInstructions.branch
    (module := module) (func := func) (le := le) (first := first) branchRun
  have branchedNew : NewPermissionInstructions module func le first before branched := by
    intro instruction member
    rcases branchNew instruction member with old | fresh
    · exact Or.inl (allocationInsts ▸ old)
    · exact Or.inr fresh
  have prefixNew := NewPermissionInstructions.append_setCur branchedNew selectRun
  have allocatedGenerated := generated.newBlock [] allocationRun
  have headerAtAllocated := newBlock_params allocationRun
  rcases headerAtAllocated with ⟨allocatedHeader, headerRow, headerParams⟩
  have headerRowAt : allocated.blocks[header]? = some allocatedHeader := by
    simpa [header] using headerRow
  have headerBoundAllocated : header < allocated.blocks.size := by
    exact (Array.getElem?_eq_some_iff.mp headerRowAt).1
  have branchedGenerated := allocatedGenerated.emitTerm (.br header []) (by
    intro target member
    simp only [Term.successors, List.mem_singleton] at member
    subst target
    exact headerBoundAllocated) branchRun
  have selectBound : header < branched.blocks.size := by
    exact Nat.lt_of_lt_of_le headerBoundAllocated
      (advB_emitTerm (.br header []) le allocated () branched branchRun).ext.1
  have selectedGenerated := branchedGenerated.setCur (some header)
    (by intro target same; cases same; exact selectBound) selectRun
  have framesBranched := (frames.mono (advB_newBlock0 le before (header, []) allocated allocationRun).ext).mono
    (advB_emitTerm (.br header []) le allocated () branched branchRun).ext
  have selectedFrames := framesBranched.of_blocks (setCur_blocks selectRun)
  have headerAtSelected : ∃ block, selected.blocks[header]? = some block ∧ block.params = [] := by
    have branchAdvance := advB_emitTerm (.br header []) le allocated () branched branchRun
    rcases branchAdvance.ext.2 header allocatedHeader headerRowAt with ⟨block', row', params', _⟩
    have same := setCur_blocks selectRun
    exact ⟨block', by rw [same]; exact row', params'.trans (by simpa [header] using headerParams)⟩
  have blockNew : ∀ {depth exit input output value},
      lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body le input = (value, output) →
      GeneratedBuilderState input → LoopBuilderFrames (some ⟨depth, exit, .jump header⟩) input →
      first ≤ input.vals.size →
      NewPermissionInstructions module func le first input output := by
    intro depth exit input output value blockRun
    intro blockGenerated blockFrames blockFloor
    exact bodyNew (header := header) (by simpa using blockRun) blockGenerated blockFrames blockFloor
  have allocationFloor := Nat.le_trans firstBound
    (advB_newBlock0 le before (header, []) allocated allocationRun).vals
  have branchFloor := Nat.le_trans allocationFloor
    (advB_emitTerm (.br header []) le allocated () branched branchRun).vals
  have selectedFloor : first ≤ selected.vals.size := by
    have sameVals : selected.vals = branched.vals := by
      rw [setCur_run] at selectRun
      rcases Prod.mk.inj selectRun with ⟨_, rfl⟩
      rfl
    simpa [sameVals] using branchFloor
  exact lowerWhile_newPermissionInstructions prefixNew whileRun selectedFloor selectedGenerated selectedFrames
    headerAtSelected conditionNew blockNew

end Goose.Lower.Validation

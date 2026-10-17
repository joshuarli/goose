import Goose.Lower.Validation.CfgSourceDominanceLive

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ssa_start_header (types : List VTy) (arguments : List ValueId)
    {env : LEnv} {before allocated closed started : LS} {header : BlockId} {params : List ValueId}
    {u₁ u₂ : Unit} (allocationRun : newBlock types env before = ((header, params), allocated))
    (closeRun : emitTerm (.br header arguments) env allocated = (u₁, closed))
    (startRun : setCur (some header) env closed = (u₂, started)) (imports : ImportedValues)
    (checked : ImportedState before imports) {source : BlockId} (current : before.cur = some source)
    (operands : AvailableValues before imports arguments) :
    ∃ nextImports, SSAResult before started imports nextImports [] ∧
      started.cur = some header ∧ AvailableValues started nextImports params := by
  have headerId : header = before.blocks.size := by
    have id := congrArg (fun step => step.1.1) allocationRun
    change before.blocks.size = header at id
    exact id.symm
  subst header
  have allocation := checked.allocate_current types env
  rw [allocationRun] at allocation
  have headerBound : before.blocks.size < allocated.blocks.size := by
    have bound := liveBound_newBlock types env before
    rw [allocationRun] at bound
    exact bound
  let nextImports := extendImports imports before.blocks.size (currentValues before imports)
  have allValues := allocation.frame _ (currentValues_available checked.opened.bound)
  have closedChecked := allocation.checked.emitTerm (.br before.blocks.size arguments) env
    (allocation.frame _ operands)
    (by intro target member; have same : target = before.blocks.size := by simpa [Term.successors] using member
        exact same.symm ▸ headerBound)
    (by intro target member; have same : target = before.blocks.size := by simpa [Term.successors] using member
        subst target; simpa [extendImports] using allValues)
  rw [closeRun] at closedChecked
  have closing := advB_emitTerm (.br before.blocks.size arguments) env allocated _ closed closeRun
  obtain ⟨body, allocationRow, opened⟩ := newBlock_open before env types
  rw [allocationRun] at allocationRow
  have allocatedCurrent : allocated.cur = some source := by
    have unchanged : (newBlock types env before).2.cur = before.cur := rfl
    rw [allocationRun] at unchanged
    exact unchanged.trans current
  have notCurrent : allocated.cur ≠ some before.blocks.size := by
    rw [allocatedCurrent]
    exact fun same => Nat.ne_of_lt (checked.opened.bound source current) (Option.some.inj same)
  have closedRow := closing.keep _ _ notCurrent allocationRow
  have selected := SSAResult.select_imports closedChecked (allocation.advance.trans closing) allocation.imports
    (by simp [current]) (Nat.lt_of_lt_of_le headerBound closing.ext.1) (Nat.le_refl _)
    ⟨_, closedRow, opened⟩ (by simp [extendImports]) env
  rw [startRun] at selected
  have startedCurrent : started.cur = some before.blocks.size := by
    rw [setCur_run] at startRun
    exact congrArg LS.cur (Prod.mk.inj startRun).2.symm
  refine ⟨nextImports, selected, startedCurrent, ?_⟩
  intro block live value member
  have equal : block = before.blocks.size := Option.some.inj (live.symm.trans startedCurrent)
  subst block
  have allocatedValue := newBlock_available_parameter (state := before) (imports := imports)
    types (currentValues before imports) (env := env) (value := value) (by rw [allocationRun]; exact member)
  rw [allocationRun] at allocatedValue
  have closedValue := allocatedValue.of_ext closing.ext (fun _ _ => rfl)
  obtain ⟨valueBody, valueRow, available⟩ := closedValue
  exact ⟨valueBody, by simpa only [← setCur_blocks startRun] using valueRow, available⟩

theorem ssa_header0 (loop : Option LoopCtx) {tail : BlockId → B Unit}
    (source : ∀ header, HeaderRun loop (.jump header) [] (tail header)) :
    LiveSSARun loop [] (fun _ => []) (do
      let (header, _) ← newBlock []
      emitTerm (.br header [])
      setCur (some header)
      tail header) := by
  intro env before result after run imports checked ready arguments live
  obtain ⟨⟨header, params⟩, allocated, allocationRun, _, closed, closeRun, _, started, startRun, tailRun⟩ :=
    (by simpa only [bind_eq] using run)
  cases current : before.cur with
  | none => simp [current] at live
  | some block =>
    obtain ⟨nextImports, startState, startedCurrent, _⟩ := ssa_start_header [] [] allocationRun closeRun startRun
      imports checked current arguments
    obtain ⟨tailImports, tailState⟩ := source header env started result after tailRun nextImports startState.checked
      (startState.loop ready) (HeaderSSA.jump_current startState.checked startedCurrent)
      (by simp [startedCurrent]) (by simp [AvailableValues])
    exact ⟨tailImports, startState.trans tailState⟩

theorem ssa_header1 (loop : Option LoopCtx) (type : IntTy) (start : ValueId) (saved : List ValueId)
    {tail : BlockId → ValueId → B Unit}
    (source : ∀ header counter, HeaderRun loop (.next header type counter) saved (tail header counter)) :
    LiveSSARun loop (start :: saved) (fun _ => []) (do
      let (header, params) ← newBlock [.data (.int type)]
      let counter := params.headD 0
      emitTerm (.br header [start])
      setCur (some header)
      tail header counter) := by
  intro env before result after run imports checked ready arguments live
  obtain ⟨⟨header, params⟩, allocated, allocationRun, _, closed, closeRun, _, started, startRun, tailRun⟩ :=
    (by simpa only [bind_eq] using run)
  cases current : before.cur with
  | none => simp [current] at live
  | some block =>
    obtain ⟨nextImports, startState, startedCurrent, parameters⟩ := ssa_start_header [.data (.int type)] [start]
      allocationRun closeRun startRun imports checked current (arguments.subset (by simp))
    have member : params.headD 0 ∈ params := by
      have ids := congrArg (fun step => step.1.2) allocationRun
      change [before.vals.size] = params at ids
      rw [← ids]
      simp
    have counterAvailable : AvailableValues started nextImports [params.headD 0] :=
      parameters.subset (by intro value entry; simpa only [List.mem_singleton.mp entry] using member)
    obtain ⟨tailImports, tailState⟩ := source header (params.headD 0) env started result after tailRun nextImports
      startState.checked (startState.loop ready)
      (HeaderSSA.next_current startState.checked startedCurrent type (params.headD 0) counterAvailable)
      (by simp [startedCurrent]) (startState.frame saved (arguments.subset (by simp)))
    exact ⟨tailImports, startState.trans tailState⟩

end Goose.Lower.Validation

import Goose.Lower.Validation.CfgSourceDominanceSourceBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ssa_sink (loop : Option LoopCtx) : LiveSSARun loop [] (fun _ => []) (do
    let (sink, _) ← newBlock []
    emitTerm (.br sink [])
    setCur (some sink)
    emitTerm (.br sink [])) := by
  apply ssa_header0 (tail := fun sink => emitTerm (.br sink []))
  intro sink env before result after run imports checked _ header _ _
  have finished := checked.emitTerm (.br sink []) env (by simp [AvailableValues, Term.uses])
    (by intro target member; have same : target = sink := by simpa [Term.successors] using member
        exact same.symm ▸ header.bound)
    (by intro target member; have same : target = sink := by simpa [Term.successors] using member
        subst target; exact header.incoming)
  rw [run] at finished
  have stopped : after.cur = none := by
    cases current : before.cur with
    | none =>
      rw [emitTerm_none (.br sink []) env current] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      exact current
    | some block =>
      rw [emitTerm_run (.br sink []) env current] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      rfl
  exact ⟨imports, SSAResult.of_current finished (advB_emitTerm _ env before _ after run)
    (Or.inl stopped) (by simp [AvailableValues])⟩

theorem ssa_finishFunction (impl : Impl) (value : ValueId) :
    SSARun none (blockValues false impl.body.value value) (fun _ => []) (finishFunction impl value) := by
  intro env before result after run imports checked ready arguments
  unfold finishFunction at run
  obtain ⟨readEnv, readState, readRun, liveRun⟩ := bind_eq.mp run
  change (env, before) = (readEnv, readState) at readRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj readRun
  obtain ⟨live, middle, currentRun, run⟩ := bind_eq.mp liveRun
  cases current : before.cur with
  | none =>
    rw [isLive_none current] at currentRun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj currentRun
    simp only [Bool.false_eq_true, ↓reduceIte] at run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    exact ⟨imports, checked, .refl before, fun _ _ => rfl, fun _ frame => frame,
      by simp [AvailableValues]⟩
  | some block =>
    rw [isLive_run current] at currentRun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj currentRun
    simp only [↓reduceIte] at run
    by_cases sink : (!impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges env.mod.noReturn) = true
    · simp only [sink, ↓reduceIte] at run
      exact ssa_sink none env before result after run imports checked ready
        (by simp [AvailableValues]) (by simp [current])
    · simp only [sink] at run
      exact ssa_emitTerm none (.ret (if impl.body.value.isSome then [value] else []) none)
        (by simp [Term.successors]) env before result after run imports checked ready
        (by simpa [Term.uses, blockValues] using arguments)

theorem ssa_function_start (types : List VTy) (continuation : List ValueId → B Unit)
    (source : ∀ params, SSARun none params (fun _ => []) (continuation params)) (env : LEnv) :
    let action : B Unit := do
      let (entry, params) ← newBlock types
      setCur (some entry)
      continuation params
    let (_, state) := action env initState
    ∃ imports, ImportedState state imports := by
  let pair := (newBlock types env initState).1
  let allocated := (newBlock types env initState).2
  let started := (setCur (some pair.1) env allocated).2
  let imports := extendImports (fun _ => []) 0 []
  have initial : ImportedState allocated imports := ImportedState.initState.newBlock types [] (by simp)
    (by simp) env
  obtain ⟨body, row, opened⟩ := newBlock_open initState env types
  have allocatedRow : allocated.blocks[pair.1]? = some body := row
  have selected : ImportedState started imports := initial.select allocatedRow opened env
  have parameters : AvailableValues started imports pair.2 := by
    intro block current value member
    have same : block = pair.1 := Option.some.inj current.symm
    subst block
    have present := newBlock_available_parameter (state := initState) (imports := fun _ => []) types [] member
    exact present
  obtain ⟨nextImports, result⟩ := source pair.2 env started _ _ rfl imports selected
    ⟨by simp [loopTargets], by simp [loopTargets], by simp [AvailableValues, loopValues]⟩ parameters
  exact ⟨nextImports, result.checked⟩

end Goose.Lower.Validation

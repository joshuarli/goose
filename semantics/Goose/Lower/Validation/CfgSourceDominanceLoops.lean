import Goose.Lower.Validation.CfgSourceDominanceLoopBody

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def HeaderRun (loop : Option LoopCtx) (continuation : ContKind) (inputs : List ValueId)
    (action : B Unit) : Prop :=
  ∀ env before result after, action env before = (result, after) →
    ∀ imports, ImportedState before imports → LoopImportsReady loop before imports →
      HeaderSSA continuation before imports → before.cur.isSome = true →
      AvailableValues before imports inputs → ∃ nextImports, SSAResult before after imports nextImports []

theorem ssa_lowerWhile (loop : Option LoopCtx) (header : BlockId) (bodyInputs : List ValueId)
    {condition : B ValueId} {body : Nat → BlockId → B ValueId}
    (conditionSource : SSARun loop [] (fun value => [value]) condition)
    (bodySource : ∀ depth exit, SSARun (some ⟨depth, exit, .jump header⟩) bodyInputs (fun _ => []) (body depth exit)) :
    HeaderRun loop (.jump header) bodyInputs (lowerWhile header condition body) := by
  intro env before result after run imports checked ready headerReady _ arguments
  unfold lowerWhile at run
  obtain ⟨value, conditioned, conditionRun, loopRun⟩ := bind_eq.mp run
  obtain ⟨conditionImports, conditionState⟩ := conditionSource env before value conditioned conditionRun
    imports checked ready (by simp [AvailableValues])
  cases current : conditioned.cur with
  | none =>
    rw [whenLive_none _ _ env current] at loopRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj loopRun
    exact ⟨conditionImports, { conditionState with available := by simp [AvailableValues] }⟩
  | some source =>
    rw [whenLive_some _ _ env current] at loopRun
    obtain ⟨nextImports, loopState⟩ := ssa_loopBody (.jump header) value bodyInputs bodySource
      (fun depth exit => ssa_emitTerm (some ⟨depth, exit, .jump header⟩) (.br header [])
        (by simp [Term.successors, loopTargets])) loopRun conditionImports conditionState.checked
      current (headerReady.move conditionState) conditionState.available (conditionState.frame bodyInputs arguments)
    exact ⟨nextImports, conditionState.trans loopState⟩

theorem ssa_lowerRange (loop : Option LoopCtx) (type : IntTy) (counter bound header : Nat)
    (bodyInputs : List ValueId) {body : Nat → BlockId → B ValueId}
    (bodySource : ∀ depth exit, SSARun (some ⟨depth, exit, .next header type counter⟩)
      (counter :: bodyInputs) (fun _ => []) (body depth exit)) :
    HeaderRun loop (.next header type counter) (bound :: bodyInputs) (lowerRange type counter bound header body) := by
  intro env before result after run imports checked ready headerReady live arguments
  unfold lowerRange at run
  obtain ⟨condition, conditioned, conditionRun, loopRun⟩ := bind_eq.mp run
  have comparisonInputs : AvailableValues before imports [counter, bound] := by
    intro block current value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with counterValue | boundValue
    · exact headerReady.counter block current value (by simpa [continuationValues] using counterValue)
    · exact arguments block current value (by simp [boundValue])
  obtain ⟨conditionImports, conditionState⟩ := ssa_emitDef loop (.cmp .lt type counter bound)
    env before condition conditioned conditionRun imports checked ready comparisonInputs
  have current : conditioned.cur = before.cur := by
    have current := emitDef_current (.cmp .lt type counter bound) env before
    rw [conditionRun] at current
    exact current
  have originalInputs : AvailableValues before imports (counter :: bodyInputs) := by
    intro block current value member
    rcases List.mem_cons.mp member with counterValue | member
    · exact headerReady.counter block current value (by simpa [continuationValues] using counterValue)
    · exact arguments block current value (by simp [member])
  cases beforeCurrent : before.cur with
  | none => simp [beforeCurrent] at live
  | some source =>
    obtain ⟨nextImports, loopState⟩ := ssa_loopBody (.next header type counter) condition (counter :: bodyInputs)
      bodySource (fun depth exit => ssa_rangeBack depth exit header type counter) loopRun conditionImports
      conditionState.checked (current.trans beforeCurrent) (headerReady.move conditionState)
      conditionState.available (conditionState.frame _ originalInputs)
    exact ⟨nextImports, conditionState.trans loopState⟩

def eachCountInputs (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) : List ValueId :=
  if regrow then [owner.getD 0] else [sampled]

theorem ssa_eachLen (loop : Option LoopCtx) (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    SSARun loop (eachCountInputs regrow owner sampled) (fun result => [result]) (eachLen regrow owner sampled) := by
  cases regrow with
  | false => exact ssa_value loop sampled
  | true => exact ssa_emitDef loop _

theorem ssa_lowerEach (loop : Option LoopCtx) (regrow : Bool) (owner : Option ValueId)
    (sampled header counter : Nat) (bodyInputs : List ValueId) {body : Nat → BlockId → B ValueId}
    (bodySource : ∀ depth exit, SSARun (some ⟨depth, exit, .next header .i64 counter⟩)
      (counter :: bodyInputs) (fun _ => []) (body depth exit)) :
    HeaderRun loop (.next header .i64 counter) (bodyInputs ++ eachCountInputs regrow owner sampled)
      (lowerEach regrow owner sampled header counter body) := by
  intro env before result after run imports checked ready headerReady live arguments
  unfold lowerEach at run
  obtain ⟨length, measured, measureRun, condition, conditioned, conditionRun, loopRun⟩ :=
    (by simpa only [bind_eq] using run)
  obtain ⟨measureImports, measuredState⟩ := ssa_eachLen loop regrow owner sampled env before length measured measureRun
    imports checked ready (arguments.subset (List.subset_append_right _ _))
  have measuredHeader := headerReady.move measuredState
  have comparisonInputs : AvailableValues measured measureImports [counter, length] := by
    intro block current value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with counterValue | lengthValue
    · exact measuredHeader.counter block current value (by simpa [continuationValues] using counterValue)
    · exact measuredState.available block current value (by simp [lengthValue])
  obtain ⟨conditionImports, conditionedState⟩ := ssa_emitDef loop (.cmp .lt .i64 counter length)
    env measured condition conditioned conditionRun measureImports measuredState.checked (measuredState.loop ready) comparisonInputs
  have history := measuredState.trans conditionedState
  have current : conditioned.cur = before.cur := by
    have conditionCurrent := emitDef_current (.cmp .lt .i64 counter length) env measured
    have measureCurrent := eachLen_current regrow owner sampled env before
    rw [conditionRun] at conditionCurrent
    rw [measureRun] at measureCurrent
    exact conditionCurrent.trans measureCurrent
  have originalInputs : AvailableValues before imports (counter :: bodyInputs) := by
    intro block current value member
    rcases List.mem_cons.mp member with counterValue | member
    · exact headerReady.counter block current value (by simpa [continuationValues] using counterValue)
    · exact arguments block current value (List.mem_append_left _ member)
  cases beforeCurrent : before.cur with
  | none => simp [beforeCurrent] at live
  | some source =>
    obtain ⟨nextImports, loopState⟩ := ssa_loopBody (.next header .i64 counter) condition (counter :: bodyInputs)
      bodySource (fun depth exit => ssa_rangeBack depth exit header .i64 counter) loopRun conditionImports
      conditionedState.checked (current.trans beforeCurrent) (headerReady.move history)
      conditionedState.available (history.frame _ originalInputs)
    exact ⟨nextImports, history.trans loopState⟩

end Goose.Lower.Validation

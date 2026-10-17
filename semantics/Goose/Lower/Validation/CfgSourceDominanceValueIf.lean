import Goose.Lower.Validation.CfgSourceDominanceArms

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ArmsSSA.joinValue {before state : LS} {beforeImports imports : ImportedValues}
    {endThen endElse : Option BlockId} {thenValue elseValue : ValueId}
    (arms : ArmsSSA before state beforeImports imports true endThen thenValue endElse elseValue)
    (initial : ImportedState before beforeImports) (live : before.cur.isSome = true) (env : LEnv) :
    ∃ nextImports, SSAResult before (Goose.Lower.joinValue endThen thenValue endElse elseValue env state).2
      beforeImports nextImports [(Goose.Lower.joinValue endThen thenValue endElse elseValue env state).1] := by
  let incoming := (endThen.map (·, thenValue)).toList ++ (endElse.map (·, elseValue)).toList
  have armData (endBlock : Option BlockId) (value : ValueId)
      (arm : ArmSSA before state beforeImports imports true endBlock value) :
      ∀ pair ∈ (endBlock.map (·, value)).toList,
        pair.1 < state.blocks.size ∧ Mine before pair.1 ∧ BuilderAvailable state imports pair.1 pair.2 ∧
          ∀ used ∈ currentValues before beforeImports, BuilderAvailable state imports pair.1 used := by
    cases endBlock with
    | none => simp
    | some block =>
      intro pair member
      have same : pair = (block, value) := by simpa using member
      subst pair
      exact ⟨arm.bounds block rfl, arm.owned block rfl, arm.operand rfl block rfl, arm.transport block rfl⟩
  have data : ∀ pair ∈ incoming,
      pair.1 < state.blocks.size ∧ Mine before pair.1 ∧ BuilderAvailable state imports pair.1 pair.2 ∧
        ∀ used ∈ currentValues before beforeImports, BuilderAvailable state imports pair.1 used := by
    intro pair member
    rcases List.mem_append.mp member with member | member
    · exact armData endThen thenValue arms.thenArm pair member
    · exact armData endElse elseValue arms.elseArm pair member
  have finished := ssa_joinLive initial arms.history live incoming
    (fun pair member => (data pair member).1)
    (fun pair member => (data pair member).2.1)
    (fun pair member => (data pair member).2.2.1)
    (fun pair member => (data pair member).2.2.2) env
  cases endThen with
  | none =>
    cases endElse with
    | none =>
      let stopped := (Goose.Lower.joinValue none thenValue none elseValue env state).2
      have checked : ImportedState stopped imports :=
        ⟨arms.history.checked.certificate.of_blocks rfl, arms.history.checked.definitions,
          arms.history.checked.targets, currentOpen_none rfl, arms.history.checked.importsBounded⟩
      have growth : state.Adv stopped := adv_joinValue (endT := none) (endF := none)
        (vt := thenValue) (vf := elseValue) (le := env) (.refl state) (by simp) (by simp) rfl
      have result : SSAResult state stopped imports imports [0] :=
        SSAResult.of_current checked growth (Or.inl rfl) (by simp [AvailableValues, stopped, Goose.Lower.joinValue, setCur_run, bind_run, pure_run])
      exact ⟨imports, arms.history.trans result⟩
    | some block =>
      exact ⟨_, by simpa only [Goose.Lower.joinValue, incoming, Option.map_none, Option.map_some,
        Option.toList_none, Option.toList_some, List.nil_append] using finished⟩
  | some block =>
    cases endElse with
    | none =>
      exact ⟨_, by simpa only [Goose.Lower.joinValue, incoming, Option.map_none, Option.map_some,
        Option.toList_none, Option.toList_some, List.append_nil] using finished⟩
    | some other =>
      exact ⟨_, by simpa only [Goose.Lower.joinValue, incoming, Option.map_some,
        Option.toList_some, List.cons_append, List.nil_append] using finished⟩

theorem ssa_recordValueRootRecipe (loop : Option LoopCtx) (value : ValueId) (sourceScope : ScopeId) :
    SSARun loop [value] (fun _ => [value]) (recordValueRootRecipe value sourceScope) := by
  intro env before result after run imports checked ready arguments
  have advance := advB_recordValueRootRecipe value sourceScope env before result after run
  rw [recordValueRootRecipe_run] at run
  obtain ⟨resultEq, afterEq⟩ := Prod.mk.inj run
  subst result
  have checkedAfter : ImportedState after imports := by
    rw [← afterEq]
    exact checked.of_tables rfl rfl rfl
  have current : after.cur = before.cur := by
    rw [← afterEq]
  refine ⟨imports, SSAResult.of_current checkedAfter advance (Or.inr current) ?_⟩
  intro block live output member
  have equal : output = value := by simpa using member
  subst output
  exact (arguments block (current.symm.trans live) value (by simp)).of_ext advance.ext (fun _ _ => rfl)

theorem ssa_ifE_core (loop : Option LoopCtx) (condition : ValueId) (sourceScope : ScopeId)
    {thenAction elseAction : B ValueId}
    (thenSource : SSARun loop [] (fun value => [value]) thenAction)
    (elseSource : SSARun loop [] (fun value => [value]) elseAction) :
    SSARun loop [condition] (fun result => [result]) (whenLive 0 fun _ => do
      let (thenBlock, elseBlock) ← fork condition
      setCur (some thenBlock)
      let thenValue ← thenAction
      let endThen ← curBlock
      setCur (some elseBlock)
      let elseValue ← elseAction
      let endElse ← curBlock
      let result ← Goose.Lower.joinValue endThen thenValue endElse elseValue
      Goose.Lower.recordValueRootRecipe result sourceScope
      pure result) := by
  intro env before result after run imports checked ready arguments
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact ⟨imports, SSAResult.of_current checked (.refl before) (Or.inr rfl)
      (by simp [AvailableValues, current])⟩
  | some start =>
    rw [whenLive_some _ _ env current] at run
    have decomposed := (by simpa only [bind_eq] using run)
    obtain ⟨⟨thenBlock, elseBlock⟩, forked, forkRun, _, thenStart, thenStartRun,
      thenValue, thenEnd, thenRun, endThen, thenRead, thenReadRun, _, elseStart, elseStartRun,
      elseValue, elseEnd, elseRun, endElse, elseRead, elseReadRun, joined, joinState, joinRun,
      recipeUnit, recipeState, recipeRun, pureRun⟩ := decomposed
    obtain ⟨thenCurrent, thenSame⟩ := curBlock_eq thenReadRun
    obtain ⟨elseCurrent, elseSame⟩ := curBlock_eq elseReadRun
    subst thenSame elseSame
    obtain ⟨armImports, arms⟩ := ssa_arms loop true condition thenSource elseSource forkRun thenStartRun
      thenRun elseStartRun elseRun imports checked ready current arguments
    obtain ⟨nextImports, joinedResult⟩ := arms.joinValue checked (by simp [current]) env
    rw [← thenCurrent, ← elseCurrent, joinRun] at joinedResult
    obtain ⟨lastImports, recipeResult⟩ := ssa_recordValueRootRecipe loop joined sourceScope
      env joinState recipeUnit recipeState recipeRun nextImports
      joinedResult.checked (joinedResult.loop ready) joinedResult.available
    change SSAResult before joinState imports nextImports [joined] at joinedResult
    rw [pure_run] at pureRun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pureRun
    exact ⟨lastImports, joinedResult.trans recipeResult⟩

end Goose.Lower.Validation

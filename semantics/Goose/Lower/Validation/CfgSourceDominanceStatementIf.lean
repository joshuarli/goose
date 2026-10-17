import Goose.Lower.Validation.CfgSourceDominanceValueIf

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ssa_joinLive0 {before state : LS} {beforeImports imports : ImportedValues}
    {values : List ValueId} (initial : ImportedState before beforeImports)
    (history : SSAResult before state beforeImports imports values) (live : before.cur.isSome = true)
    (incoming : List BlockId) (bounds : ∀ block ∈ incoming, block < state.blocks.size)
    (owned : ∀ block ∈ incoming, Mine before block)
    (transport : ∀ block ∈ incoming, ∀ value ∈ currentValues before beforeImports,
      BuilderAvailable state imports block value) (env : LEnv) :
    let action : B Unit := do
      let (join, _) ← newBlock []
      patchBrs0 join incoming
      setCur (some join)
    SSAResult before (action env state).2 beforeImports
      (extendImports imports state.blocks.size (currentValues before beforeImports)) [] := by
  dsimp only
  let captured := currentValues before beforeImports
  let allocated := (newBlock [] env state).2
  let nextImports := extendImports imports state.blocks.size captured
  let patched := (patchBrs0 state.blocks.size incoming env allocated).2
  let joined := (setCur (some state.blocks.size) env patched).2
  have entry : state.blocks.size = 0 → captured = [] := by
    intro empty
    cases current : before.cur with
    | none => simp [currentValues, captured, current]
    | some block =>
      have bound := Nat.lt_of_lt_of_le (initial.opened.bound block current) history.advance.ext.1
      rw [empty] at bound
      exact False.elim (Nat.not_lt_zero _ bound)
  have capturedBound : ∀ value ∈ captured, value < state.vals.size := by
    intro value member
    exact Nat.lt_of_lt_of_le
      (currentValues_bounded initial.definitions initial.opened.bound initial.importsBounded value member)
      history.advance.vals
  have allocation := history.checked.allocate [] captured entry capturedBound env
  have oldImports : ∀ block, block < state.blocks.size → nextImports block = imports block := allocation.imports
  have allocatedTransport : ∀ block ∈ incoming, ∀ value ∈ nextImports state.blocks.size,
      BuilderAvailable allocated nextImports block value := by
    intro block member value imported
    have imported : value ∈ captured := by simpa [nextImports, extendImports] using imported
    exact (transport block member value imported).of_ext allocation.advance.ext oldImports
  have patchedCertificate := allocation.checked.certificate.patchBrs0 state.blocks.size incoming env allocatedTransport
  have allocatedJoinBound : state.blocks.size < allocated.blocks.size := by simp [allocated, newBlock0_run]
  have patchedTargets := targets_patchBrs0 state.blocks.size incoming env allocated allocation.checked.targets allocatedJoinBound
  have patchedDefinitions := dense_patchBrs0 state.blocks.size incoming env allocated _ patched rfl
    allocation.checked.definitions allocation.checked.opened.bound
  have patchSize : patched.blocks.size = allocated.blocks.size := (patchBrs0_size incoming rfl).symm
  have patchValues : patched.vals = allocated.vals := patchBrs0_values _ _ _ _
  have patchedRow : patched.blocks[state.blocks.size]? = some ⟨[], #[]⟩ := by
    rw [patchBrs0_other state.blocks.size incoming env allocated state.blocks.size
      (fun block member => Nat.ne_of_lt (bounds block member))]
    simp [allocated, newBlock0_run]
  have joinedChecked : ImportedState joined nextImports := by
    refine ⟨patchedCertificate.of_blocks rfl, patchedDefinitions.1, patchedTargets,
      CurrentOpen.setCur patchedRow (open_empty _) env, ?_⟩
    intro block bound value imported
    change value < patched.vals.size
    rw [patchValues]
    exact allocation.checked.importsBounded block
      (by change block < patched.blocks.size at bound; simpa only [patchSize] using bound) value imported
  have patchedAdvance : before.Adv patched :=
    adv_patchBrs0 incoming (history.advance.trans allocation.advance) owned rfl
  have joinedAdvance : before.Adv joined := adv_setCur_step (le := env) patchedAdvance
    (Or.inr history.advance.ext.1) (Nat.lt_of_lt_of_le allocatedJoinBound (Nat.le_of_eq patchSize.symm)) rfl
  have importsPrefix : ∀ block, block < before.blocks.size → nextImports block = beforeImports block := by
    intro block bound
    exact (oldImports block (Nat.lt_of_lt_of_le bound history.advance.ext.1)).trans (history.imports block bound)
  exact SSAResult.of_imports joinedChecked joinedAdvance importsPrefix live rfl
    (by intro value member; simpa [nextImports, extendImports] using member) (by simp [AvailableValues])

theorem ArmsSSA.joinArms {before state : LS} {beforeImports imports : ImportedValues}
    {endThen endElse : Option BlockId} {thenValue elseValue : ValueId}
    (arms : ArmsSSA before state beforeImports imports false endThen thenValue endElse elseValue)
    (initial : ImportedState before beforeImports) (live : before.cur.isSome = true) (env : LEnv) :
    ∃ nextImports, SSAResult before (Goose.Lower.joinArms endThen endElse env state).2 beforeImports nextImports [] := by
  let incoming := endThen.toList ++ endElse.toList
  have armData (endBlock : Option BlockId) (value : ValueId)
      (arm : ArmSSA before state beforeImports imports false endBlock value) :
      ∀ block ∈ endBlock.toList, block < state.blocks.size ∧ Mine before block ∧
        ∀ used ∈ currentValues before beforeImports, BuilderAvailable state imports block used := by
    cases endBlock with
    | none => simp
    | some source =>
      intro block member
      have same : block = source := by simpa using member
      subst block
      exact ⟨arm.bounds source rfl, arm.owned source rfl, arm.transport source rfl⟩
  have data : ∀ block ∈ incoming, block < state.blocks.size ∧ Mine before block ∧
      ∀ used ∈ currentValues before beforeImports, BuilderAvailable state imports block used := by
    intro block member
    rcases List.mem_append.mp member with member | member
    · exact armData endThen thenValue arms.thenArm block member
    · exact armData endElse elseValue arms.elseArm block member
  have finished := ssa_joinLive0 initial arms.history live incoming (fun block member => (data block member).1)
    (fun block member => (data block member).2.1) (fun block member => (data block member).2.2) env
  cases endThen with
  | none =>
    cases endElse with
    | none =>
      let stopped := (Goose.Lower.joinArms none none env state).2
      have checked : ImportedState stopped imports :=
        ⟨arms.history.checked.certificate.of_blocks rfl, arms.history.checked.definitions,
          arms.history.checked.targets, currentOpen_none rfl, arms.history.checked.importsBounded⟩
      have growth : state.Adv stopped := adv_joinArms (endT := none) (endF := none) (le := env)
        (.refl state) (by simp) (by simp) rfl
      exact ⟨imports, arms.history.trans (SSAResult.of_current checked growth (Or.inl rfl) (by simp [AvailableValues]))⟩
    | some block => exact ⟨_, by simpa only [Goose.Lower.joinArms, incoming, Option.toList_none,
        Option.toList_some, List.nil_append] using finished⟩
  | some block =>
    cases endElse with
    | none => exact ⟨_, by simpa only [Goose.Lower.joinArms, incoming, Option.toList_none,
        Option.toList_some, List.append_nil] using finished⟩
    | some other => exact ⟨_, by simpa only [Goose.Lower.joinArms, incoming, Option.toList_some,
        List.cons_append, List.nil_append] using finished⟩

theorem ssa_ifS_some_core (loop : Option LoopCtx) (condition : ValueId) {thenAction elseAction : B ValueId}
    (thenSource : SSARun loop [] (fun _ => []) thenAction) (elseSource : SSARun loop [] (fun _ => []) elseAction) :
    SSARun loop [condition] (fun _ => []) (whenLive () fun _ => do
      let (thenBlock, elseBlock) ← fork condition
      setCur (some thenBlock)
      let _thenValue ← thenAction
      let endThen ← curBlock
      setCur (some elseBlock)
      let _elseValue ← elseAction
      let endElse ← curBlock
      Goose.Lower.joinArms endThen endElse) := by
  intro env before result after run imports checked ready arguments
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact ⟨imports, SSAResult.of_current checked (.refl before) (Or.inr rfl) (by simp [AvailableValues])⟩
  | some start =>
    rw [whenLive_some _ _ env current] at run
    obtain ⟨⟨thenBlock, elseBlock⟩, forked, forkRun, _, thenStart, thenStartRun,
      thenValue, thenEnd, thenRun, endThen, thenRead, thenReadRun, _, elseStart, elseStartRun,
      elseValue, elseEnd, elseRun, endElse, elseRead, elseReadRun, joinRun⟩ := (by simpa only [bind_eq] using run)
    obtain ⟨thenCurrent, thenSame⟩ := curBlock_eq thenReadRun
    obtain ⟨elseCurrent, elseSame⟩ := curBlock_eq elseReadRun
    subst thenSame elseSame
    obtain ⟨armImports, arms⟩ := ssa_arms loop false condition thenSource elseSource forkRun thenStartRun
      thenRun elseStartRun elseRun imports checked ready current arguments
    obtain ⟨nextImports, finished⟩ := arms.joinArms checked (by simp [current]) env
    rw [← thenCurrent, ← elseCurrent, joinRun] at finished
    exact ⟨nextImports, finished⟩

end Goose.Lower.Validation

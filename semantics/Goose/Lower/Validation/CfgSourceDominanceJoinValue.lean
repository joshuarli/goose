import Goose.Lower.Validation.CfgSourceDominancePatches

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ssa_joinLive {before state : LS} {beforeImports imports : ImportedValues}
    {values : List ValueId} (initial : ImportedState before beforeImports)
    (history : SSAResult before state beforeImports imports values) (live : before.cur.isSome = true)
    (incoming : List (BlockId × ValueId))
    (bounds : ∀ pair ∈ incoming, pair.1 < state.blocks.size)
    (owned : ∀ pair ∈ incoming, Mine before pair.1)
    (operands : ∀ pair ∈ incoming, BuilderAvailable state imports pair.1 pair.2)
    (transport : ∀ pair ∈ incoming, ∀ value ∈ currentValues before beforeImports,
      BuilderAvailable state imports pair.1 value) (env : LEnv) :
    let action : B ValueId := do
      let ty ← valTy (incoming.headD (0, 0)).2
      let (join, params) ← newBlock [ty]
      patchBrs join incoming
      setCur (some join)
      pure (params.headD 0)
    SSAResult before (action env state).2 beforeImports
      (extendImports imports state.blocks.size (currentValues before beforeImports)) [(action env state).1] := by
  dsimp only
  let captured := currentValues before beforeImports
  let ty := (valTy (incoming.headD (0, 0)).2 env state).1
  have readRun : valTy (incoming.headD (0, 0)).2 env state = (ty, state) := by
    have same := valTy_run (incoming.headD (0, 0)).2 env state
    exact Prod.ext rfl same
  let allocated := (newBlock [ty] env state).2
  let nextImports := extendImports imports state.blocks.size captured
  let patched := (patchBrs state.blocks.size incoming env allocated).2
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
  have allocation := history.checked.allocate [ty] captured entry capturedBound env
  have oldImports : ∀ block, block < state.blocks.size → nextImports block = imports block := allocation.imports
  have allocatedOperands : ∀ pair ∈ incoming, BuilderAvailable allocated nextImports pair.1 pair.2 := by
    intro pair member
    exact (operands pair member).of_ext allocation.advance.ext oldImports
  have allocatedTransport : ∀ pair ∈ incoming, ∀ value ∈ nextImports state.blocks.size,
      BuilderAvailable allocated nextImports pair.1 value := by
    intro pair member value imported
    have imported : value ∈ captured := by simpa [nextImports, extendImports] using imported
    exact (transport pair member value imported).of_ext allocation.advance.ext oldImports
  have patchedCertificate := allocation.checked.certificate.patchBrs state.blocks.size incoming env
    allocatedOperands allocatedTransport
  have allocatedJoinBound : state.blocks.size < allocated.blocks.size := by
    simp [allocated, newBlock1_run]
  have patchedTargets := targets_patchBrs state.blocks.size incoming env allocated allocation.checked.targets
    allocatedJoinBound
  have patchedDefinitions := dense_patchBrs state.blocks.size incoming env allocated _ patched rfl
    allocation.checked.definitions allocation.checked.opened.bound
  have patchSize : patched.blocks.size = allocated.blocks.size := (patchBrs_size incoming rfl).symm
  have patchValues : patched.vals = allocated.vals := patchBrs_values _ _ _ _
  have patchedRow : patched.blocks[state.blocks.size]? = some ⟨[(state.vals.size, ty)], #[]⟩ := by
    rw [patchBrs_other state.blocks.size incoming env allocated state.blocks.size
      (fun pair member => Nat.ne_of_lt (bounds pair member))]
    simp [allocated, newBlock1_run]
  have joinedRow : joined.blocks[state.blocks.size]? = some ⟨[(state.vals.size, ty)], #[]⟩ := by
    simpa only [joined, setCur_run] using patchedRow
  have joinedChecked : ImportedState joined nextImports := by
    refine ⟨patchedCertificate.of_blocks rfl, patchedDefinitions.1, patchedTargets,
      CurrentOpen.setCur patchedRow (open_empty _) env, ?_⟩
    intro block bound value imported
    change value < patched.vals.size
    rw [patchValues]
    exact allocation.checked.importsBounded block
      (by change block < patched.blocks.size at bound; simpa only [patchSize] using bound) value imported
  have patchedAdvance : before.Adv patched :=
    adv_patchBrs incoming (history.advance.trans allocation.advance) owned rfl
  have joinedAdvance : before.Adv joined := adv_setCur_step (le := env) patchedAdvance
    (Or.inr history.advance.ext.1) (Nat.lt_of_lt_of_le allocatedJoinBound (Nat.le_of_eq patchSize.symm)) rfl
  have importsPrefix : ∀ block, block < before.blocks.size → nextImports block = beforeImports block := by
    intro block bound
    exact (oldImports block (Nat.lt_of_lt_of_le bound history.advance.ext.1)).trans (history.imports block bound)
  have joinedCurrent : joined.cur = some state.blocks.size := rfl
  have finalResult : SSAResult before joined beforeImports nextImports [state.vals.size] := by
    refine ⟨joinedChecked, joinedAdvance, importsPrefix, ?_, ?_⟩
    · intro saved available block current value member
      have same : block = state.blocks.size := Option.some.inj (current.symm.trans joinedCurrent)
      subst block
      cases original : before.cur with
      | none => simp [original] at live
      | some source =>
        have imported : value ∈ captured := by
          simpa [captured, currentValues, original] using
            (available source original value member).exitValues
        exact ⟨_, joinedRow, Or.inl (by simpa [nextImports, extendImports] using imported)⟩
    · intro block current value member
      have sameValue : value = state.vals.size := by simpa using member
      subst value
      have same : block = state.blocks.size := Option.some.inj (current.symm.trans joinedCurrent)
      subst block
      exact ⟨_, joinedRow, Or.inr (by simp [cfgBlock, GIR.Block.defs])⟩
  have actionRun :
      ((do
        let ty ← valTy (incoming.headD (0, 0)).2
        let (join, params) ← newBlock [ty]
        patchBrs join incoming
        setCur (some join)
        pure (params.headD 0) : B ValueId) env state) = (state.vals.size, joined) := by
    simp only [bind_run, readRun, newBlock1_run, List.headD_cons, pure_run]
    rfl
  simpa only [actionRun] using finalResult

end Goose.Lower.Validation

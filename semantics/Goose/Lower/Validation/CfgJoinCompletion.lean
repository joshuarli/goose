import Goose.Lower.Validation.CfgPatchCompletion

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem joinLive_complete (incoming : List (BlockId × ValueId))
    (unique : (incoming.map Prod.fst).Nodup) (env : LEnv) (state : LS)
    (shaped : ShapedBlocks state)
    (openIncoming : ∀ pair ∈ incoming, ∃ body, state.blocks[pair.1]? = some body ∧ OpenBlock body) :
    let action : B ValueId := do
      let ty ← valTy (incoming.headD (0, 0)).2
      let (join, params) ← newBlock [ty]
      patchBrs join incoming
      setCur (some join)
      pure (params.headD 0)
    ShapedBlocks (action env state).2 ∧
      OpenCount (action env state).2 + incoming.length = OpenCount state + 1 := by
  cases read : valTy (incoming.headD (0, 0)).2 env state with
  | mk ty unchanged =>
    have same := valTy_run (incoming.headD (0, 0)).2 env state
    rw [read] at same
    dsimp only at same
    subst unchanged
    let initial := (newBlock [ty] env state).2
    have initialShaped := shaped.newBlock [ty] env
    have initialCount := openCount_newBlock state [ty] env
    have initialOpen : ∀ pair ∈ incoming, ∃ body, initial.blocks[pair.1]? = some body ∧ OpenBlock body := by
      intro pair member
      obtain ⟨body, row, openBody⟩ := openIncoming pair member
      have bound := (Array.getElem?_eq_some_iff.mp row).1
      exact ⟨body, (newBlock_other state env [ty] pair.1 bound).trans row, openBody⟩
    obtain ⟨shapePatched, countPatched⟩ := patchBrs_complete state.blocks.size env incoming unique
      initial initialShaped initialOpen
    simp only [bind_run, read, newBlock1_run, setCur_run, pure_run]
    refine ⟨shapePatched.of_blocks rfl, ?_⟩
    change OpenCount (patchBrs state.blocks.size incoming env initial).2 + incoming.length = OpenCount state + 1
    dsimp only [initial] at countPatched ⊢
    omega

theorem joinEmpty_complete (incoming : List BlockId) (unique : incoming.Nodup)
    (env : LEnv) (state : LS) (shaped : ShapedBlocks state)
    (openIncoming : ∀ block ∈ incoming, ∃ body, state.blocks[block]? = some body ∧ OpenBlock body) :
    let action : B Unit := do
      let (join, _) ← newBlock []
      patchBrs0 join incoming
      setCur (some join)
    ShapedBlocks (action env state).2 ∧
      OpenCount (action env state).2 + incoming.length = OpenCount state + 1 := by
  let initial := (newBlock [] env state).2
  have initialShaped := shaped.newBlock [] env
  have initialCount := openCount_newBlock state [] env
  have initialOpen : ∀ block ∈ incoming, ∃ body, initial.blocks[block]? = some body ∧ OpenBlock body := by
    intro block member
    obtain ⟨body, row, openBody⟩ := openIncoming block member
    have bound := (Array.getElem?_eq_some_iff.mp row).1
    exact ⟨body, (newBlock_other state env [] block bound).trans row, openBody⟩
  obtain ⟨shapePatched, countPatched⟩ := patchBrs0_complete state.blocks.size env incoming unique
    initial initialShaped initialOpen
  simp only [bind_run, newBlock0_run, setCur_run]
  refine ⟨shapePatched.of_blocks rfl, ?_⟩
  change OpenCount (patchBrs0 state.blocks.size incoming env initial).2 + incoming.length = OpenCount state + 1
  dsimp only [initial] at countPatched ⊢
  omega

theorem joinValue_complete (endT endF : Option BlockId) (valueT valueF : ValueId)
    (env : LEnv) (state : LS) (shaped : ShapedBlocks state)
    (unique : (((endT.map (·, valueT)).toList ++ (endF.map (·, valueF)).toList).map Prod.fst).Nodup)
    (openIncoming : ∀ pair ∈ (endT.map (·, valueT)).toList ++ (endF.map (·, valueF)).toList,
      ∃ body, state.blocks[pair.1]? = some body ∧ OpenBlock body) :
    ShapedBlocks (joinValue endT valueT endF valueF env state).2 ∧
      OpenCount (joinValue endT valueT endF valueF env state).2 +
          endT.toList.length + endF.toList.length =
        OpenCount state + LiveCount (joinValue endT valueT endF valueF env state).2 := by
  cases endT with
  | none =>
    cases endF with
    | none =>
      refine ⟨shaped.of_blocks rfl, ?_⟩
      simp [joinValue, bind_run, setCur_run, pure_run, OpenCount, LiveCount]
    | some block =>
      have live : LiveCount (joinValue none valueT (some block) valueF env state).2 = 1 := rfl
      obtain ⟨shape, count⟩ := joinLive_complete [(block, valueF)] (by simp)
        env state shaped (by simpa using openIncoming)
      refine ⟨shape, ?_⟩
      simp only [live, Option.toList_none, List.length_nil, Nat.add_zero,
        Option.toList_some, List.length_singleton]
      exact count
  | some block =>
    cases endF with
    | none =>
      have live : LiveCount (joinValue (some block) valueT none valueF env state).2 = 1 := rfl
      obtain ⟨shape, count⟩ := joinLive_complete [(block, valueT)] (by simp)
        env state shaped (by simpa using openIncoming)
      refine ⟨shape, ?_⟩
      simp only [live, Option.toList_none, List.length_nil, Nat.add_zero,
        Option.toList_some, List.length_singleton]
      exact count
    | some other =>
      have live : LiveCount (joinValue (some block) valueT (some other) valueF env state).2 = 1 := rfl
      obtain ⟨shape, count⟩ := joinLive_complete [(block, valueT), (other, valueF)]
        (by simpa using unique) env state shaped (by simpa using openIncoming)
      refine ⟨shape, ?_⟩
      simp only [live, Option.toList_some, List.length_cons, List.length_nil,
        Nat.add_assoc]
      change OpenCount (joinValue (some block) valueT (some other) valueF env state).2 + 2 = _ at count
      omega

theorem joinArms_complete (endT endF : Option BlockId) (env : LEnv) (state : LS)
    (shaped : ShapedBlocks state) (unique : (endT.toList ++ endF.toList).Nodup)
    (openIncoming : ∀ block ∈ endT.toList ++ endF.toList,
      ∃ body, state.blocks[block]? = some body ∧ OpenBlock body) :
    ShapedBlocks (joinArms endT endF env state).2 ∧
      OpenCount (joinArms endT endF env state).2 + endT.toList.length + endF.toList.length =
        OpenCount state + LiveCount (joinArms endT endF env state).2 := by
  cases endT with
  | none =>
    cases endF with
    | none =>
      refine ⟨shaped.of_blocks rfl, ?_⟩
      simp [joinArms, setCur_run, OpenCount, LiveCount]
    | some block =>
      have live : LiveCount (joinArms none (some block) env state).2 = 1 := rfl
      obtain ⟨shape, count⟩ := joinEmpty_complete [block] (by simp)
        env state shaped (by simpa using openIncoming)
      refine ⟨shape, ?_⟩
      simp only [live, Option.toList_none, List.length_nil, Nat.add_zero,
        Option.toList_some, List.length_singleton]
      exact count
  | some block =>
    cases endF with
    | none =>
      have live : LiveCount (joinArms (some block) none env state).2 = 1 := rfl
      obtain ⟨shape, count⟩ := joinEmpty_complete [block] (by simp)
        env state shaped (by simpa using openIncoming)
      refine ⟨shape, ?_⟩
      simp only [live, Option.toList_none, List.length_nil, Nat.add_zero,
        Option.toList_some, List.length_singleton]
      exact count
    | some other =>
      have live : LiveCount (joinArms (some block) (some other) env state).2 = 1 := rfl
      obtain ⟨shape, count⟩ := joinEmpty_complete [block, other]
        (by simpa using unique) env state shaped (by simpa using openIncoming)
      refine ⟨shape, ?_⟩
      simp only [live, Option.toList_some, List.length_cons, List.length_nil, Nat.add_assoc]
      change OpenCount (joinArms (some block) (some other) env state).2 + 2 = _ at count
      omega

end Goose.Lower.Validation

import Goose.Lower.Frag

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR

theorem graphExtension_sameBlocks {before after : LS} (blocks : after.blocks = before.blocks) :
    before.Ext after := by
  constructor
  · exact blocks ▸ Nat.le_refl before.blocks.size
  · intro index block row
    exact ⟨block, blocks ▸ row, rfl, [], by simp⟩

theorem joinValue_graphExtension (endYes endNo : Option BlockId) (yes no : ValueId)
    (le : LEnv) (state : LS) : state.Ext (Goose.Lower.joinValue endYes yes endNo no le state).2 := by
  generalize run : Goose.Lower.joinValue endYes yes endNo no le state = result
  rcases result with ⟨value, after⟩
  unfold Goose.Lower.joinValue at run
  have active : ∀ live : List (BlockId × ValueId),
      (do
        let type ← valTy (live.headD (0, 0)).2
        let (target, parameters) ← newBlock [type]
        patchBrs target live
        setCur (some target)
        pure (parameters.headD 0) : B ValueId) le state = (value, after) → state.Ext after := by
    intro live lowered
    simp only [bind_eq] at lowered
    obtain ⟨type, queried, query, ⟨target, parameters⟩, allocated, allocate,
      patchedResult, patched, patch, selectedResult, selected, select, returned⟩ := lowered
    have unchanged := valTy_eq query
    subst queried
    have allocation := (adv_newBlock1 allocate).ext
    have patchedExtension := adv_patchBrs_ext live patch
    rw [setCur_run] at select
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj select
    rw [pure_run] at returned
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj returned
    exact allocation.trans patchedExtension
  cases endYes <;> cases endNo
  · simp only [bind_eq, setCur_run, pure_run] at run
    obtain ⟨result, selected, selectedRun, returned⟩ := run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj selectedRun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj returned
    exact graphExtension_sameBlocks rfl
  · exact active _ run
  · exact active _ run
  · exact active _ run

theorem joinArms_graphExtension (endYes endNo : Option BlockId) (le : LEnv) (state : LS) :
    state.Ext (joinArms endYes endNo le state).2 := by
  generalize run : joinArms endYes endNo le state = result
  rcases result with ⟨value, after⟩
  unfold joinArms at run
  have active : ∀ live : List BlockId,
      (do
        let (target, _) ← newBlock []
        patchBrs0 target live
        setCur (some target) : B Unit) le state = (value, after) → state.Ext after := by
    intro live lowered
    simp only [bind_eq] at lowered
    obtain ⟨⟨target, parameters⟩, allocated, allocate, patchedResult, patched, patch, select⟩ := lowered
    have allocation := (adv_newBlock0 allocate).ext
    have patchedExtension := adv_patchBrs0_ext live patch
    rw [setCur_run] at select
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj select
    exact allocation.trans patchedExtension
  cases endYes <;> cases endNo
  · change setCur none le state = (value, after) at run
    rw [setCur_run] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact graphExtension_sameBlocks rfl
  · exact active _ run
  · exact active _ run
  · exact active _ run

#print axioms graphExtension_sameBlocks
#print axioms joinValue_graphExtension
#print axioms joinArms_graphExtension

end Goose.Lower.Validation.ReplacementContentFlowSource

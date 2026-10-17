import Goose.Lower.Validation.ActualContentsJoinEdges

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem actualContents_joinLive_arguments {le : LEnv} {before after : LS}
    {incoming : List (BlockId × ValueId)} {type : VTy} {value : ValueId}
    (typed : before.vals[(incoming.headD (0, 0)).2]? = some (some type))
    (sources : ∀ pair ∈ incoming, pair.1 < before.blocks.size)
    (run : (do
      let valueType ← valTy (incoming.headD (0, 0)).2
      let (join, params) ← newBlock [valueType]
      patchBrs join incoming
      setCur (some join)
      pure (params.headD 0)) le before = (value, after))
    (ambient : ActualContentsAmbient le after) (allowed : ambient.authorized value) :
    ∀ pair ∈ incoming, ambient.authorized pair.2 := by
  simp only [bind_run, valTy_of_recorded typed, newBlock1_run] at run
  let allocated : LS := { before with
    blocks := before.blocks.push ⟨[(before.vals.size, type)], #[]⟩
    vals := before.vals.push (some type) }
  cases patched : patchBrs before.blocks.size incoming le allocated with
  | mk patchResult middle =>
    change (do
      patchBrs before.blocks.size incoming
      setCur (some before.blocks.size)
      pure before.vals.size) le allocated = (value, after) at run
    simp only [bind_run, patched, setCur_run, pure_run] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    let middleAmbient := ambient.before (LS.Ext.refl middle)
      (types_setCur (some before.blocks.size) le middle () _ rfl)
    exact middleAmbient.patchBrs_arguments incoming
      (by intro pair member; exact Nat.lt_trans (sources pair member) (by simp [allocated]))
      (destination := ⟨[(before.vals.size, type)], []⟩)
      (by simp [permissionFunc, allocated, Array.getElem_push]) rfl patched allowed

theorem actualContents_joinValue_arguments {le : LEnv} {before after : LS}
    {endT endF : Option BlockId} {valueT valueF value : ValueId} {type : VTy}
    (thenBound : ∀ block, endT = some block → block < before.blocks.size)
    (elseBound : ∀ block, endF = some block → block < before.blocks.size)
    (thenTyped : endT.isSome = true → before.vals[valueT]? = some (some type))
    (elseTyped : endF.isSome = true → before.vals[valueF]? = some (some type))
    (run : joinValue endT valueT endF valueF le before = (value, after))
    (live : after.cur.isSome = true) (ambient : ActualContentsAmbient le after)
    (allowed : ambient.authorized value) :
    (endT.isSome = true → ambient.authorized valueT) ∧
      (endF.isSome = true → ambient.authorized valueF) := by
  cases endT with
  | none =>
    cases endF with
    | none =>
      simp only [joinValue, bind_run, setCur_run, pure_run] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      simp at live
    | some block =>
      have arguments := actualContents_joinLive_arguments (incoming := [(block, valueF)])
        (elseTyped rfl) (by intro pair member; obtain rfl := List.mem_singleton.mp member; exact elseBound block rfl)
        run ambient allowed
      exact ⟨by simp, fun _ => arguments (block, valueF) (by simp)⟩
  | some block =>
    cases endF with
    | none =>
      have arguments := actualContents_joinLive_arguments (incoming := [(block, valueT)])
        (thenTyped rfl) (by intro pair member; obtain rfl := List.mem_singleton.mp member; exact thenBound block rfl)
        run ambient allowed
      exact ⟨fun _ => arguments (block, valueT) (by simp), by simp⟩
    | some other =>
      have arguments := actualContents_joinLive_arguments (incoming := [(block, valueT), (other, valueF)])
        (thenTyped rfl) (by
          intro pair member
          rcases List.mem_cons.mp member with rfl | member
          · exact thenBound block rfl
          · obtain rfl := List.mem_singleton.mp member
            exact elseBound other rfl) run ambient allowed
      exact ⟨fun _ => arguments (block, valueT) (by simp), fun _ => arguments (other, valueF) (by simp)⟩

theorem actualContents_joinValue_ext {endT endF : Option BlockId} {vt vf : ValueId} {le : LEnv} {ls : LS}
    {r : ValueId} {ls' : LS} (h : joinValue endT vt endF vf le ls = (r, ls')) : ls.Ext ls' := by
  unfold joinValue at h
  have key : ∀ {live : List (BlockId × ValueId)},
      (do
        let ty ← valTy (live.headD (0, 0)).2
        let (jb, js) ← newBlock [ty]
        patchBrs jb live
        setCur (some jb)
        pure (js.headD 0) : B ValueId) le ls = (r, ls') → ls.Ext ls' := by
    intro live hk
    simp only [bind_eq] at hk
    obtain ⟨ty, ls2, h1, ⟨jb, js⟩, ls3, h2, u, ls4, h3, u2, ls5, h4, hp⟩ := hk
    have hls2 : ls2 = ls := valTy_eq h1
    subst hls2
    have e2 := (adv_newBlock1 h2).ext
    have e3 := adv_patchBrs_ext live h3
    rw [setCur_run] at h4
    obtain ⟨-, rfl⟩ := Prod.mk.inj h4
    rw [pure_run] at hp
    obtain ⟨-, rfl⟩ := Prod.mk.inj hp
    exact e2.trans e3
  cases endT <;> cases endF
  · simp only [bind_eq] at h
    obtain ⟨u, ls2, h1, hp⟩ := h
    rw [setCur_run] at h1
    obtain ⟨-, rfl⟩ := Prod.mk.inj h1
    rw [pure_run] at hp
    obtain ⟨-, rfl⟩ := Prod.mk.inj hp
    exact LS.Ext.refl _
  all_goals exact key h

end Goose.Lower.Validation

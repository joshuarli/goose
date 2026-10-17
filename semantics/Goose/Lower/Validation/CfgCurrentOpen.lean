import Goose.Lower.Validation.CfgLoopComposition

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def CurrentOpen (state : LS) : Prop :=
  ∀ block, state.cur = some block →
    ∃ body, state.blocks[block]? = some body ∧ OpenBlock body

theorem CurrentOpen.bound {state : LS} (openCurrent : CurrentOpen state) : LiveBound state := by
  intro block current
  obtain ⟨body, row, _⟩ := openCurrent block current
  exact (Array.getElem?_eq_some_iff.mp row).1

theorem CurrentOpen.row {state : LS} (openCurrent : CurrentOpen state) {block : BlockId} {body : BlockB}
    (current : state.cur = some block) (row : state.blocks[block]? = some body) : OpenBlock body := by
  obtain ⟨other, otherRow, openBody⟩ := openCurrent block current
  have equal : other = body := Option.some.inj (otherRow.symm.trans row)
  exact equal ▸ openBody

theorem currentOpen_none {state : LS} (stopped : state.cur = none) : CurrentOpen state := by
  intro block current
  rw [stopped] at current
  cases current

theorem CurrentOpen.of_state {before after : LS} (openCurrent : CurrentOpen before)
    (blocks : after.blocks = before.blocks) (current : after.cur = before.cur) : CurrentOpen after := by
  intro block live
  rw [current] at live
  obtain ⟨body, row, openBody⟩ := openCurrent block live
  exact ⟨body, by simpa [blocks] using row, openBody⟩

theorem CurrentOpen.setCur {state : LS} {block : BlockId} {body : BlockB}
    (row : state.blocks[block]? = some body) (openBody : OpenBlock body) (env : LEnv) :
    CurrentOpen (setCur (some block) env state).2 := by
  rw [setCur_run]
  intro target current
  have equal : block = target := Option.some.inj current
  exact ⟨body, by simpa [← equal] using row, openBody⟩

theorem CurrentOpen.emitDef {state : LS} (openCurrent : CurrentOpen state) (op : Op) (env : LEnv) :
    CurrentOpen (emitDef op env state).2 := by
  intro block current
  have beforeCurrent : state.cur = some block := (emitDef_current op env state).symm.trans current
  obtain ⟨body, row, openBody⟩ := openCurrent block beforeCurrent
  exact emitDef_open beforeCurrent row openBody op env

theorem CurrentOpen.emitEffect {state : LS} (openCurrent : CurrentOpen state) (effect : Effect) (env : LEnv) :
    CurrentOpen (emitEffect effect env state).2 := by
  cases current : state.cur with
  | none => rw [emitEffect_none effect env current]; exact openCurrent
  | some block =>
    obtain ⟨body, row, openBody⟩ := openCurrent block current
    have emitted := emitEffect_open current row openBody effect env
    intro target live
    rw [emitEffect_run effect env current] at live
    have equal : block = target := Option.some.inj (current.symm.trans live)
    simpa [← equal] using emitted

theorem currentOpen_emitTerm (state : LS) (term : Term) (env : LEnv) :
    CurrentOpen (emitTerm term env state).2 := by
  apply currentOpen_none
  cases current : state.cur with
  | none => rw [emitTerm_none term env current]; exact current
  | some block => rw [emitTerm_run term env current]

theorem CurrentOpen.newBlock {state : LS} (openCurrent : CurrentOpen state)
    (types : List VTy) (env : LEnv) : CurrentOpen (newBlock types env state).2 := by
  intro block current
  have beforeCurrent : state.cur = some block := current
  obtain ⟨body, row, openBody⟩ := openCurrent block beforeCurrent
  have bound := (Array.getElem?_eq_some_iff.mp row).1
  exact ⟨body, (newBlock_other state env types block bound).trans row, openBody⟩

theorem adv_current_ne_old {before after : LS} (advance : before.Adv after) {block : BlockId}
    (bound : block < before.blocks.size) (different : before.cur ≠ some block) : after.cur ≠ some block := by
  intro current
  rcases advance.cur with stopped | same | ⟨fresh, freshCurrent, newBlock, _⟩
  · rw [stopped] at current
    cases current
  · exact different (same.symm.trans current)
  · have equal := Option.some.inj (freshCurrent.symm.trans current)
    subst fresh
    exact Nat.not_le_of_gt bound newBlock

end Goose.Lower.Validation

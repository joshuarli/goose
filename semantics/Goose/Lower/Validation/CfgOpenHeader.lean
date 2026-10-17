import Goose.Lower.Validation.CfgOpenLoop

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem opens_header0 {tail : BlockId → B Unit}
    (tailOpen : ∀ header, LiveOpenRun (tail header)) :
    LiveOpenRun (do
      let (header, _) ← newBlock []
      emitTerm (.br header [])
      setCur (some header)
      tail header) := by
  intro env before result after run _ bounded live
  cases current : before.cur with
  | none => simp [current] at live
  | some source =>
    simp only [bind_eq] at run
    obtain ⟨⟨header, params⟩, initial, newRun, _, closed, closeRun, _, started, startRun, tailRun⟩ := run
    rw [newBlock0_run] at newRun
    obtain ⟨pairEq, stateEq⟩ := Prod.mk.inj newRun
    obtain ⟨headerEq, _⟩ := Prod.mk.inj pairEq
    subst header
    subst initial
    have initialCurrent : ({ before with blocks := before.blocks.push ⟨[], #[]⟩ } : LS).cur = some source := current
    have different : source ≠ before.blocks.size := Nat.ne_of_lt (bounded source current)
    have closedRow : closed.blocks[before.blocks.size]? = some ⟨[], #[]⟩ := by
      rw [emitTerm_run _ env initialCurrent] at closeRun
      obtain ⟨_, same⟩ := Prod.mk.inj closeRun
      rw [← same]
      simp only [Array.getElem?_modify, different, ite_false]
      simp
    have startedOpen := CurrentOpen.setCur closedRow (open_empty _) env
    rw [startRun] at startedOpen
    have startedLive : started.cur.isSome = true := by
      rw [setCur_current startRun]
      rfl
    exact tailOpen _ env started result after tailRun startedOpen startedOpen.bound startedLive

theorem opens_header1 (ty : VTy) (value : ValueId) {tail : BlockId → ValueId → B Unit}
    (tailOpen : ∀ header counter, LiveOpenRun (tail header counter)) :
    LiveOpenRun (do
      let (header, params) ← newBlock [ty]
      emitTerm (.br header [value])
      setCur (some header)
      tail header (params.headD 0)) := by
  intro env before result after run _ bounded live
  cases current : before.cur with
  | none => simp [current] at live
  | some source =>
    simp only [bind_eq] at run
    obtain ⟨⟨header, params⟩, initial, newRun, _, closed, closeRun, _, started, startRun, tailRun⟩ := run
    rw [newBlock1_run] at newRun
    obtain ⟨pairEq, stateEq⟩ := Prod.mk.inj newRun
    obtain ⟨headerEq, _⟩ := Prod.mk.inj pairEq
    subst header
    subst initial
    have initialCurrent : ({ before with blocks := before.blocks.push ⟨[(before.vals.size, ty)], #[]⟩, vals := before.vals.push (some ty) } : LS).cur = some source := current
    have different : source ≠ before.blocks.size := Nat.ne_of_lt (bounded source current)
    have closedRow : closed.blocks[before.blocks.size]? = some ⟨[(before.vals.size, ty)], #[]⟩ := by
      rw [emitTerm_run _ env initialCurrent] at closeRun
      obtain ⟨_, same⟩ := Prod.mk.inj closeRun
      rw [← same]
      simp only [Array.getElem?_modify, different, ite_false]
      simp
    have startedOpen := CurrentOpen.setCur closedRow (open_empty _) env
    rw [startRun] at startedOpen
    have startedLive : started.cur.isSome = true := by
      rw [setCur_current startRun]
      rfl
    exact tailOpen _ _ env started result after tailRun startedOpen startedOpen.bound startedLive

end Goose.Lower.Validation

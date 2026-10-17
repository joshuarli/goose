import Goose.Lower.Validation.CfgLoopPaths

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def LivePathRun (action : B α) : Prop :=
  ∀ env before result after, action env before = (result, after) →
    ReachableBuilder before → LiveBound before → before.cur.isSome = true → ReachableBuilder after

theorem LivePathRun.of_bounded {action : B α} (preserves : BoundedRun ReachableBuilder action) :
    LivePathRun action := fun env before result after run paths bounded _ =>
  preserves env before result after run paths bounded

theorem paths_header0 {tail : BlockId → B Unit} (tailPaths : ∀ header, LivePathRun (tail header)) :
    LivePathRun (do
      let (header, _) ← newBlock []
      emitTerm (.br header [])
      setCur (some header)
      tail header) := by
  intro env before result after run paths bounded live
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
    have initialCurrent : ({ before with blocks := before.blocks.push ⟨[], #[]⟩ } : LS).cur =
        some source := current
    have patchedPaths := paths.newBlock0_patchBrs0 (bounded source current) [] env
    have closedPaths : ReachableBuilder closed := by
      apply patchedPaths.of_blocks
      rw [emitTerm_run _ env initialCurrent] at closeRun
      obtain ⟨_, stateEq⟩ := Prod.mk.inj closeRun
      rw [← stateEq]
      rfl
    have startedPaths := closedPaths.of_blocks (setCur_blocks startRun)
    have closeSize : closed.blocks.size = before.blocks.size + 1 := by
      rw [emitTerm_run _ env initialCurrent] at closeRun
      obtain ⟨_, stateEq⟩ := Prod.mk.inj closeRun
      rw [← stateEq]
      simp
    have headerBound : before.blocks.size < closed.blocks.size := by rw [closeSize]; omega
    have startedBound := liveBound_setCur headerBound env
    rw [startRun] at startedBound
    have startedLive : started.cur.isSome = true := by
      rw [setCur_run] at startRun
      obtain ⟨_, stateEq⟩ := Prod.mk.inj startRun
      rw [← stateEq]
      rfl
    exact tailPaths _ env started result after tailRun startedPaths startedBound startedLive

end Goose.Lower.Validation

import Goose.Lower.Validation.SummaryPreservationRefinedAppend

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem initSlots_refined_witness {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {ls final : LS} {le : LEnv} {resultUnit : Unit}
    (bindings : List (SlotId × ValueId × OriginId))
    (current : ls.CurrentBlocks)
    (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (roots : ∀ binding ∈ bindings, ∀ root ∈ rootsAt upper.vals binding.2.1,
      root ∈ rootsAt upper.slots binding.1)
    (run : initSlots bindings le ls = (resultUnit, final)) :
    BuilderRootWitness results vt func upper final ∧
      BuilderEffectRefinement module vt func upper source final ∧
      final.CurrentBlocks ∧ final.vals = ls.vals ∧ final.cur = ls.cur ∧
      final.blocks.size = ls.blocks.size := by
  induction bindings generalizing ls final with
  | nil =>
    change ((), ls) = (resultUnit, final) at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact ⟨witness, prior, current, rfl, rfl, rfl⟩
  | cons binding rest ih =>
    rcases binding with ⟨slot, value, origin⟩
    obtain ⟨first, mid, firstRun, tail⟩ := bind_eq.mp run
    have tailRoots := fun binding member => roots binding (List.mem_cons_of_mem _ member)
    cases currentRow : ls.cur with
    | none =>
      rw [emitEffect_none _ _ currentRow] at firstRun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj firstRun
      simpa [currentRow] using ih current witness prior tailRoots tail
    | some block =>
      rw [emitEffect_run _ _ currentRow] at firstRun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj firstRun
      have blockBound := current block currentRow
      have closed : InstructionRootsClosed results vt
          { func with blocks := finishBlocks ls.blocks } upper (.eff (.slotInit slot value (some origin))) :=
        roots (slot, value, origin) (by simp)
      have generated := appendInst_refined_witness blockBound witness prior closed
        (effectRefinement_empty func source)
      have nextCurrent : (ls.appendInst block (.eff (.slotInit slot value (some origin)))).CurrentBlocks := by
        intro candidate candidateRow
        simpa [LS.appendInst] using current candidate candidateRow
      have remaining := ih nextCurrent generated.1 generated.2 tailRoots tail
      refine ⟨remaining.1, remaining.2.1, remaining.2.2.1, remaining.2.2.2.1,
        ?_, ?_⟩
      · simpa [LS.appendInst, currentRow] using remaining.2.2.2.2.1
      · simpa [LS.appendInst] using remaining.2.2.2.2.2

end Goose.Lower.Validation.SummaryPreservation

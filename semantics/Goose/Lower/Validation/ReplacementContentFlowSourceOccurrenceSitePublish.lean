import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceSites

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR

theorem OccurrenceSitesBuilder.emitReplacement {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before after : LS} {func : Func} {types : Array (Option VTy)} {old next : Prov}
    {owner value : ValueId} {origin : OriginId}
    (checked : OccurrenceSitesBuilder env root targets le before func types old)
    (run : Goose.Lower.emitEffect (.replace owner value (some origin)) le before = ((), after))
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ index, index < old.vals.size → rootsAt next.vals index = rootsAt old.vals index)
    (source : ∀ block body, before.cur = some block → before.blocks[block]? = some body →
      Nonempty (SiteOccurrences env root targets le after func types next block body.insts.size owner value origin)) :
    OccurrenceSitesBuilder env root targets le after func types next := by
  have extension := (advB_emitEffect (.replace owner value (some origin)) le before () after run).ext
  have preserved : ReplacementIntervalsPreserved targets before after :=
    .of_run (generatedTargetFrame_emitEffect none _) run
  have typePrefix := types_emitEffect (.replace owner value (some origin)) le before () after run
  cases current : before.cur with
  | none =>
    rw [emitEffect_none _ _ current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    intro block body row position inst lookup
    exact (checked block body row position inst lookup).retained (.refl before) (.refl before)
      (fun _ _ _ _ framed => framed) growth retained
  | some index =>
    rw [emitEffect_run _ _ current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    intro block body row position instruction lookup
    change (before.blocks.modify index (fun body =>
      { body with insts := body.insts.push (.eff (.replace owner value (some origin))) }))[block]? = some body at row
    rw [Array.getElem?_modify] at row
    by_cases same : index = block
    · subst block
      simp only [ite_true] at row
      cases oldRow : before.blocks[index]? with
      | none => simp [oldRow] at row
      | some previous =>
        simp only [oldRow, Option.map_some, Option.some.injEq] at row
        subst body
        change (previous.insts.push (.eff (.replace owner value (some origin))))[position]? = some instruction at lookup
        by_cases fresh : position = previous.insts.size
        · subst position
          simp only [Array.getElem?_push_eq, Option.some.injEq] at lookup
          subst instruction
          exact source index previous current oldRow
        · rw [Array.getElem?_push, if_neg fresh] at lookup
          exact (checked index previous oldRow position instruction lookup).retained extension typePrefix preserved growth retained
    · simp only [same, ite_false] at row
      exact (checked block body row position instruction lookup).retained extension typePrefix preserved growth retained

#print axioms OccurrenceSitesBuilder.emitReplacement

end Goose.Lower.Validation.ReplacementContentFlowSource

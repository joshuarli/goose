import Goose.Lower.Validation.ReplacementRegions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem closedBlock_prefix_shape {before after : BlockB} {extra : List Inst}
    (closed : ClosedBlock after) (append : after.insts.toList = before.insts.toList ++ extra) :
    OpenBlock before ∨ ClosedBlock before := by
  by_cases opened : (cfgBlock before).terms = []
  · exact Or.inl opened
  have termCount := closed.1
  change (after.insts.toList.filterMap Inst.term?).length = 1 at termCount
  rw [append, List.filterMap_append, List.length_append] at termCount
  have beforePositive : 0 < (before.insts.toList.filterMap Inst.term?).length := by
    change (before.insts.toList.filterMap Inst.term?) ≠ [] at opened
    exact List.length_pos_iff.mpr opened
  have noTerms : extra.filterMap Inst.term? = [] :=
    List.eq_nil_of_length_eq_zero (by omega)
  have empty : extra = [] := by
    cases lastAt : extra.getLast? with
    | none => exact List.getLast?_eq_none_iff.mp lastAt
    | some inst =>
      have last := closed.2
      simp only [cfgBlock, GIR.Block.lastTerm?, append, List.getLast?_append, lastAt, Option.or_some] at last
      cases inst with
      | «def» value op => simp [Option.or] at last
      | eff effect => simp [Option.or] at last
      | term term =>
        have member : term ∈ extra.filterMap Inst.term? :=
          List.mem_filterMap.mpr ⟨.term term, List.mem_of_getLast? lastAt, rfl⟩
        simp [noTerms] at member
  right
  simpa only [ClosedBlock, cfgBlock, GIR.Block.terms, GIR.Block.lastTerm?, append,
    empty, List.append_nil] using closed

theorem shaped_of_closed_extension {before after : LS} (extension : before.Ext after)
    (closed : ∀ body ∈ after.blocks.toList, ClosedBlock body) : ∀ (index : BlockId) (body : BlockB), before.blocks[index]? = some body → OpenBlock body ∨ ClosedBlock body := by
  intro index body row
  obtain ⟨finalBody, finalAt, _, extra, append⟩ := extension.2 index body row
  exact closedBlock_prefix_shape
    (closed finalBody (Array.mem_toList_iff.mpr (Array.mem_of_getElem? finalAt))) append

end Goose.Lower.Validation

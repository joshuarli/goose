import Goose.Lower.Validation.SummaryPreservationRefinedAppend

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem patchBrs_refined_witness {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {ls final : LS} {le : LEnv} {join : BlockId} {unit : Unit}
    (edges : List (BlockId × ValueId))
    (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (bounds : ∀ pair ∈ edges, pair.1 < ls.blocks.size)
    (roots : ∀ pair ∈ edges,
      EdgeRootsClosed { func with blocks := finishBlocks ls.blocks } upper join [pair.2])
    (run : patchBrs join edges le ls = (unit, final)) :
    BuilderRootWitness results vt func upper final ∧
      BuilderEffectRefinement module vt func upper source final ∧
      final.blocks.size = ls.blocks.size ∧ final.vals = ls.vals ∧
      BlockParametersAgree { func with blocks := finishBlocks ls.blocks }
        { func with blocks := finishBlocks final.blocks } := by
  induction edges generalizing ls final with
  | nil =>
    change ((), ls) = (unit, final) at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact ⟨witness, prior, rfl, rfl, fun _ => rfl⟩
  | cons pair rest ih =>
    obtain ⟨first, mid, patched, tail⟩ := bind_eq.mp run
    rw [patchTerm_run] at patched
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj patched
    have bound := bounds pair (by simp)
    have closed : InstructionRootsClosed results vt
        { func with blocks := finishBlocks ls.blocks } upper (.term (.br join [pair.2])) :=
      roots pair (by simp)
    have completed := appendInst_refined_witness bound witness prior closed
      (effectRefinement_empty func source)
    have parameters := appendInst_block_parameters func ls pair.1 (.term (.br join [pair.2]))
    have remaining := ih completed.1 completed.2
      (fun next member => by simpa [LS.appendInst] using bounds next (by simp [member]))
      (fun next member => edge_roots_closed_function_shape parameters (roots next (by simp [member]))) tail
    refine ⟨remaining.1, remaining.2.1, ?_, remaining.2.2.2.1, ?_⟩
    · simpa [LS.appendInst] using remaining.2.2.1
    · intro target
      exact (parameters target).trans (remaining.2.2.2.2 target)

end Goose.Lower.Validation.SummaryPreservation

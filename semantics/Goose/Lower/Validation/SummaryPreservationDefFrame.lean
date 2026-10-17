import Goose.Lower.Validation.SummaryPreservationRefinedBuilder

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem emitDef_refined_frame_growth {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} (op : Op)
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (uses : ∀ value ∈ op.uses, value < ls.vals.size)
    (origin : ∀ org, op.origin = some org → org < le.mod.origins.size)
    (references : Op.SymbolRefsValid le op)
    (delta : EffectRefinement func (func.effectStep module vt upper {} (.def ls.vals.size op)) source) :
    ∃ next : Prov, BuilderRootWitness results vt func next (emitDef op le ls).2 ∧
      BuilderEffectRefinement module vt func next source (emitDef op le ls).2 ∧
      rootsAt next.vals (emitDef op le ls).1 =
        rootsOfDef results vt func upper (emitDef op le ls).1 op ∧ next.slots = upper.slots ∧
      (emitDef op le ls).2.SymbolWF le scopeCount ∧ (emitDef op le ls).2.cur = some block ∧
      block < (emitDef op le ls).2.blocks.size ∧ (emitDef op le ls).1 < (emitDef op le ls).2.vals.size ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨next, rootWitness, effects, returned, slots, growth⟩ := emitDef_refined_witness_growth
    symbols current blockBound witness prior (op := op)
    (value := (emitDef op le ls).1) (final := (emitDef op le ls).2) uses delta rfl
  refine ⟨next, rootWitness, effects, returned, slots, ?_, ?_, ?_, ?_, growth⟩
  · rw [emitDef_run _ _ current]
    exact symbols.emitDef current blockBound (Inst.SymbolsWithin.def uses origin references)
  · rw [emitDef_run _ _ current]
    exact current
  · rw [emitDef_run _ _ current]
    simpa using blockBound
  · rw [emitDef_run _ _ current]
    simp

end Goose.Lower.Validation.SummaryPreservation

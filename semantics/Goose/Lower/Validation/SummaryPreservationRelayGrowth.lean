import Goose.Lower.Validation.SummaryPreservationDefFrame

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem emitDef_relay_refined_witness_growth {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {sourceRoots : List RootRef} {ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {operand : ValueId} (op : Op)
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (roots : RootsRefine func (rootsAt upper.vals operand) sourceRoots)
    (uses : ∀ value ∈ op.uses, value < ls.vals.size)
    (origin : ∀ org, op.origin = some org → org < le.mod.origins.size)
    (references : Op.SymbolRefsValid le op)
    (relay : rootsOfDef results vt func upper ls.vals.size op = rootsAt upper.vals operand)
    (neutral : func.effectStep module vt upper {} (.def ls.vals.size op) = {}) :
    ∃ next : Prov, BuilderRootWitness results vt func next (emitDef op le ls).2 ∧
      BuilderEffectRefinement module vt func next source (emitDef op le ls).2 ∧
      RootsRefine func (rootsAt next.vals (emitDef op le ls).1) sourceRoots ∧ next.slots = upper.slots ∧
      (emitDef op le ls).2.SymbolWF le scopeCount ∧ (emitDef op le ls).2.cur = some block ∧
      block < (emitDef op le ls).2.blocks.size ∧ (emitDef op le ls).1 < (emitDef op le ls).2.vals.size ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have delta : EffectRefinement func (func.effectStep module vt upper {} (.def ls.vals.size op)) source := by
    rw [neutral]
    exact effectRefinement_empty func source
  obtain ⟨next, rootWitness, effects, returned, slots, nextSymbols, nextCurrent,
    nextBlockBound, nextValueBound, growth⟩ := emitDef_refined_frame_growth op symbols current
    blockBound witness prior uses origin references delta
  refine ⟨next, rootWitness, effects, ?_, slots, nextSymbols, nextCurrent, nextBlockBound, nextValueBound, growth⟩
  rw [returned]
  have value : (emitDef op le ls).1 = ls.vals.size := by rw [emitDef_run _ _ current]
  rw [value, relay]
  exact roots

end Goose.Lower.Validation.SummaryPreservation

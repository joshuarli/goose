import Goose.Lower.Validation.SummaryPreservationEmit
import Goose.Lower.Validation.SummaryPreservationEffectGrowth
import Goose.Lower.Validation.SummaryPreservationEffectRefinement

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def BuilderEffectRefinement (module : GIR.Module) (vt : Array (Option VTy))
    (func : Func) (upper : Prov) (source : Core.Eff) (ls : LS) : Prop :=
  ∀ inst ∈ ls.insts, EffectRefinement func (func.effectStep module vt upper {} inst) source

theorem emitDef_refined_witness_seeded_growth {module : GIR.Module} {res : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {upper : Prov} {source : Core.Eff}
    {ls final : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId} {op : Op}
    {value : ValueId} (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness res vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (uses : ∀ used ∈ op.uses, used < ls.vals.size)
    (delta : EffectRefinement func (func.effectStep module vt upper {} (.def ls.vals.size op)) source)
    (chosen : List RootRef)
    (included : rootsOfDef res vt func upper value op ⊆ chosen)
    (run : emitDef op le ls = (value, final)) :
    ∃ next : Prov, BuilderRootWitness res vt func next final ∧
      BuilderEffectRefinement module vt func next source final ∧
      rootsAt next.vals value = chosen ∧
      next.slots = upper.slots ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨next, nextWitness, roots, slots, growth⟩ :=
    emitDef_root_witness_seeded_growth symbols current blockBound witness uses chosen included run
  refine ⟨next, nextWitness, ?_, roots, slots, growth⟩
  rw [emitDef_run op le current] at run
  cases run
  intro inst member
  have membership : inst ∈ ls.insts ++ [.def ls.vals.size op] :=
    (LS.insts.modifyPush blockBound (.def ls.vals.size op)).mem_iff.mp member
  have stable (bounds : ∀ used ∈ inst.uses, used < ls.vals.size) :
      func.effectStep module vt next {} inst = func.effectStep module vt upper {} inst := by
    apply effectStep_congr_values inst
    intro used usedMember
    apply growth used
    rw [witness.valueSize]
    exact bounds used usedMember
  rcases List.mem_append.mp membership with old | added
  · rw [stable (symbols.instructions inst old).uses]
    exact prior inst old
  · have same := List.mem_singleton.mp added
    subst inst
    rw [stable uses]
    exact delta

theorem emitDef_refined_witness_growth {module : GIR.Module} {res : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {upper : Prov} {source : Core.Eff}
    {ls final : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId} {op : Op}
    {value : ValueId} (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness res vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (uses : ∀ used ∈ op.uses, used < ls.vals.size)
    (delta : EffectRefinement func (func.effectStep module vt upper {} (.def ls.vals.size op)) source)
    (run : emitDef op le ls = (value, final)) :
    ∃ next : Prov, BuilderRootWitness res vt func next final ∧
      BuilderEffectRefinement module vt func next source final ∧
      rootsAt next.vals value = rootsOfDef res vt func upper value op ∧
      next.slots = upper.slots ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  exact emitDef_refined_witness_seeded_growth symbols current blockBound witness prior uses delta
    (rootsOfDef res vt func upper value op) (fun _ member => member) run

theorem emitDef_refined_witness {module : GIR.Module} {res : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {upper : Prov} {source : Core.Eff}
    {ls final : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId} {op : Op}
    {value : ValueId} (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness res vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (uses : ∀ used ∈ op.uses, used < ls.vals.size)
    (delta : EffectRefinement func (func.effectStep module vt upper {} (.def ls.vals.size op)) source)
    (run : emitDef op le ls = (value, final)) :
    ∃ next : Prov, BuilderRootWitness res vt func next final ∧
      BuilderEffectRefinement module vt func next source final ∧
      rootsAt next.vals value = rootsOfDef res vt func upper value op ∧
      next.slots = upper.slots := by
  obtain ⟨next, rootWitness, effects, roots, slots, _⟩ := emitDef_refined_witness_growth
    symbols current blockBound witness prior uses delta run
  exact ⟨next, rootWitness, effects, roots, slots⟩

end Goose.Lower.Validation.SummaryPreservation

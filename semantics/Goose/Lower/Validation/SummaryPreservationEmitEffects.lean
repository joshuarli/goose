import Goose.Lower.Validation.SummaryPreservationEmit
import Goose.Lower.Validation.SummaryPreservationEffectGrowth

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def BuilderEffectsBound (module : GIR.Module) (vt : Array (Option VTy))
    (func : Func) (upper : Prov) (source : Core.Eff) (ls : LS) : Prop :=
  ∀ inst ∈ ls.insts, EffectReplay func (func.effectStep module vt upper {} inst) source

theorem emitDef_root_effect_witness {module : GIR.Module} {res : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {upper : Prov} {source : Core.Eff}
    {ls final : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId} {op : Op}
    {value : ValueId} (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness res vt func upper ls)
    (prior : BuilderEffectsBound module vt func upper source ls)
    (uses : ∀ used ∈ op.uses, used < ls.vals.size)
    (delta : EffectReplay func (func.effectStep module vt upper {} (.def ls.vals.size op)) source)
    (run : emitDef op le ls = (value, final)) :
    ∃ next : Prov, BuilderRootWitness res vt func next final ∧
      BuilderEffectsBound module vt func next source final ∧
      rootsAt next.vals value = rootsOfDef res vt func upper value op ∧
      next.slots = upper.slots := by
  obtain ⟨next, nextWitness, roots, slots, growth⟩ :=
    emitDef_root_witness_growth symbols current blockBound witness uses run
  refine ⟨next, nextWitness, ?_, roots, slots⟩
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

end Goose.Lower.Validation.SummaryPreservation

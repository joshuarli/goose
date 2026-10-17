import Goose.Lower.Validation.SummaryPreservationEmitEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem appendInst_root_effect_witness {module : GIR.Module}
    {res : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {ls : LS} {block : BlockId} {inst : Inst}
    (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness res vt func upper ls)
    (prior : BuilderEffectsBound module vt func upper source ls)
    (roots : InstructionRootsClosed res vt { func with blocks := finishBlocks ls.blocks } upper inst)
    (delta : EffectReplay func (func.effectStep module vt upper {} inst) source) :
    BuilderRootWitness res vt func upper (ls.appendInst block inst) ∧
      BuilderEffectsBound module vt func upper source (ls.appendInst block inst) := by
  have membership {instruction : Inst} (member : instruction ∈ (ls.appendInst block inst).insts) :
      instruction ∈ ls.insts ∨ instruction = inst := by
    have original := (LS.insts.modifyPush blockBound inst).mem_iff.mp member
    simpa using original
  refine ⟨⟨witness.valueSize, ?_⟩, ?_⟩
  · intro instruction member
    apply instruction_roots_closed_function_shape
      (before := { func with blocks := finishBlocks ls.blocks })
      (after := { func with blocks := finishBlocks (ls.appendInst block inst).blocks })
      rfl rfl (appendInst_block_parameters func ls block inst)
    rcases membership member with old | same
    · exact witness.instructions instruction old
    · simpa only [same] using roots
  · intro instruction member
    rcases membership member with old | same
    · exact prior instruction old
    · simpa only [same] using delta

theorem emitEffect_root_effect_witness {module : GIR.Module}
    {res : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {ls : LS} {le : LEnv} {block : BlockId} {effect : Effect}
    (current : ls.cur = some block) (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness res vt func upper ls)
    (prior : BuilderEffectsBound module vt func upper source ls)
    (roots : InstructionRootsClosed res vt { func with blocks := finishBlocks ls.blocks } upper (.eff effect))
    (delta : EffectReplay func (func.effectStep module vt upper {} (.eff effect)) source) :
    BuilderRootWitness res vt func upper (emitEffect effect le ls).2 ∧
      BuilderEffectsBound module vt func upper source (emitEffect effect le ls).2 := by
  rw [emitEffect_run effect le current]
  exact appendInst_root_effect_witness blockBound witness prior roots delta

theorem emitTerm_root_effect_witness {module : GIR.Module}
    {res : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {ls : LS} {le : LEnv} {block : BlockId} {term : Term}
    (current : ls.cur = some block) (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness res vt func upper ls)
    (prior : BuilderEffectsBound module vt func upper source ls)
    (roots : InstructionRootsClosed res vt { func with blocks := finishBlocks ls.blocks } upper (.term term))
    (delta : EffectReplay func (func.effectStep module vt upper {} (.term term)) source) :
    BuilderRootWitness res vt func upper (emitTerm term le ls).2 ∧
      BuilderEffectsBound module vt func upper source (emitTerm term le ls).2 := by
  have result := appendInst_root_effect_witness blockBound witness prior roots delta
  rw [emitTerm_run term le current]
  exact ⟨⟨result.1.valueSize, result.1.instructions⟩, result.2⟩

end Goose.Lower.Validation.SummaryPreservation

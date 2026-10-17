import Goose.Lower.Validation.SummaryPreservationLocalReads
import Goose.Lower.Validation.SummaryPreservationEmitEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem lowerExpr_read_var_summary_witness {module : GIR.Module}
    {res : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {ls : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId} {env : PEnv} {varId : VarId}
    {localVar : LocalVar} {sourceRoots : List RootRef} {start finish : RState}
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness res vt func upper ls)
    (prior : BuilderEffectsBound module vt func upper start.eff ls)
    (slotBound : varId < le.slots.size)
    (checked : checkAnnotationShape env.mod env.impl env.ctx = .ok ())
    (variableRow : env.impl.vars[varId]? = some localVar)
    (source : rpExpr env (.read (.var varId)) start = .ok (sourceRoots, finish))
    (slotRoots : RootsRepresent func (rootsAt upper.slots varId) (env.ann varId |>.getD [])) :
    ∃ next : Prov, BuilderRootWitness res vt func next (lowerExpr (.read (.var varId)) le ls).2 ∧
      BuilderEffectsBound module vt func next finish.eff (lowerExpr (.read (.var varId)) le ls).2 ∧
      RootsRepresent func (rootsAt next.vals (lowerExpr (.read (.var varId)) le ls).1) sourceRoots ∧
      next.slots = upper.slots := by
  rw [rpExpr_read_variable] at source
  have state := readRoots_variable_state variableRow source
  subst finish
  let address := lowerPlace (.var varId) le ls
  obtain ⟨middle, middleWitness, middleEffects, addressRoots, sameSlots⟩ :=
    emitDef_root_effect_witness symbols current blockBound witness prior
      (op := .slotAddr varId) (value := address.1) (final := address.2)
      (by simp [Op.uses]) (effectReplay_empty func start.eff) rfl
  have middleSymbols := lowerPlace_var_symbols symbols current blockBound varId slotBound
  have middleCurrent : address.2.cur = some block := by
    dsimp [address, lowerPlace]
    rw [emitDef_run _ _ current]
    exact current
  have middleBlockBound : block < address.2.blocks.size := by
    dsimp [address, lowerPlace]
    rw [emitDef_run _ _ current]
    simpa using blockBound
  have addressBound : address.1 < address.2.vals.size := by
    dsimp [address, lowerPlace]
    rw [emitDef_run _ _ current]
    simp
  have represented : RootsRepresent func
      (rootsOfDef res vt func middle address.2.vals.size (.load address.1)) sourceRoots := by
    apply readRoots_variable_load_represent_of_annotations checked variableRow source addressRoots
    rw [sameSlots]
    exact slotRoots
  have delta : EffectReplay func
      (func.effectStep module vt middle {} (.def address.2.vals.size (.load address.1))) start.eff := by
    change EffectReplay func { reads := addTargets [] (rootsTargets (rootsAt middle.vals address.1)) } start.eff
    rw [addressRoots]
    exact effectReplay_empty func start.eff
  obtain ⟨next, nextWitness, nextEffects, roots, slots⟩ := emitDef_root_effect_witness
    middleSymbols middleCurrent middleBlockBound middleWitness middleEffects
    (op := .load address.1) (value := (emitDef (.load address.1) le address.2).1)
    (final := (emitDef (.load address.1) le address.2).2)
    (by simpa [Op.uses] using addressBound) delta rfl
  refine ⟨next, nextWitness, nextEffects, ?_, slots.trans sameSlots⟩
  change RootsRepresent func
    (rootsAt next.vals (emitDef (.load address.1) le address.2).1) sourceRoots
  rw [roots]
  have value : (emitDef (.load address.1) le address.2).1 = address.2.vals.size := by
    rw [emitDef_run _ _ middleCurrent]
  rw [value]
  exact represented

end Goose.Lower.Validation.SummaryPreservation

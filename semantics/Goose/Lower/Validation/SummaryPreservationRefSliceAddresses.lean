import Goose.Lower.Validation.SummaryPreservationTypedSlots
import Goose.Lower.Validation.SummaryPreservationRefinedReads

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rootsOfDef_load_refSlice_slot {env : PEnv} {varId : VarId} {localVar : LocalVar}
    {res : Array (List RootRef)} {vt : Array (Option VTy)} {provenance : Prov}
    {result address : ValueId}
    (variableRow : env.impl.vars[varId]? = some localVar)
    (reference : localVar.ty.isRefSlice = true)
    (addressRoots : rootsAt provenance.vals address = [.local varId])
    (slots : provenance.slots = typedContextSlotUpper env.mod env.ctx env.impl)
    (resultType : vt[result]? = some (some (.data localVar.ty))) :
    rootsOfDef res vt (lowerContextAt env.mod env.ctx env.impl) provenance result (.load address) =
      [.param varId] := by
  have refLike : localVar.ty.isRefLike = true := by
    cases type : localVar.ty <;> simp_all [Ty.isRefSlice, Ty.isRefLike]
  rw [rootsOfDef_load_slot addressRoots]
  have recognized : valRefLike vt result = true := by
    simp [valRefLike, resultType, VTy.refLike, refLike]
  simp only [recognized, ite_true, slots, typedContextSlotUpper_at variableRow, reference]

theorem lowerExpr_refSlice_address_source_witness {module : GIR.Module}
    {env : PEnv} {res : Array (List RootRef)} {vt : Array (Option VTy)} {upper : Prov}
    {ls : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId} {varId : VarId}
    {localVar : LocalVar} {sourceRoots : List RootRef} {start finish : RState}
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness res vt (lowerContextAt env.mod env.ctx env.impl) upper ls)
    (prior : BuilderEffectRefinement module vt (lowerContextAt env.mod env.ctx env.impl) upper start.eff ls)
    (slotBound : varId < le.slots.size)
    (variableRow : env.impl.vars[varId]? = some localVar)
    (source : rpExpr env (.read (.var varId)) start = .ok (sourceRoots, finish))
    (reference : localVar.ty.isRefSlice = true)
    (slotRoots : upper.slots = typedContextSlotUpper env.mod env.ctx env.impl)
    (resultType : vt[(lowerPlace (.var varId) le ls).2.vals.size]? = some (some (.data localVar.ty))) :
    ∃ next : Prov, BuilderRootWitness res vt (lowerContextAt env.mod env.ctx env.impl) next (lowerExpr (.read (.var varId)) le ls).2 ∧
      BuilderEffectRefinement module vt (lowerContextAt env.mod env.ctx env.impl) next finish.eff (lowerExpr (.read (.var varId)) le ls).2 ∧
      rootsAt next.vals (lowerExpr (.read (.var varId)) le ls).1 = [.param varId] ∧
      next.slots = upper.slots := by
  rw [rpExpr_read_variable] at source
  have state := readRoots_variable_state variableRow source
  subst finish
  let address := lowerPlace (.var varId) le ls
  obtain ⟨middle, middleWitness, middleEffects, addressRoots, sameSlots⟩ :=
    emitDef_refined_witness symbols current blockBound witness prior
      (op := .slotAddr varId) (value := address.1) (final := address.2)
      (by simp [Op.uses]) (effectRefinement_empty (lowerContextAt env.mod env.ctx env.impl) start.eff) rfl
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
  have exactRoots : rootsOfDef res vt (lowerContextAt env.mod env.ctx env.impl)
      middle address.2.vals.size (.load address.1) = [.param varId] := by
    apply rootsOfDef_load_refSlice_slot variableRow reference addressRoots _ resultType
    exact sameSlots.trans slotRoots
  have delta : EffectRefinement (lowerContextAt env.mod env.ctx env.impl)
      ((lowerContextAt env.mod env.ctx env.impl).effectStep module vt middle {} (.def address.2.vals.size (.load address.1))) start.eff := by
    change EffectRefinement (lowerContextAt env.mod env.ctx env.impl) { reads := addTargets [] (rootsTargets (rootsAt middle.vals address.1)) } start.eff
    rw [addressRoots]
    exact effectRefinement_empty (lowerContextAt env.mod env.ctx env.impl) start.eff
  obtain ⟨next, nextWitness, nextEffects, roots, slots⟩ := emitDef_refined_witness
    middleSymbols middleCurrent middleBlockBound middleWitness middleEffects
    (op := .load address.1) (value := (emitDef (.load address.1) le address.2).1)
    (final := (emitDef (.load address.1) le address.2).2)
    (by simpa [Op.uses] using addressBound) delta rfl
  have recorded : BuilderRootWitness res vt (lowerContextAt env.mod env.ctx env.impl) next
        (lowerExpr (.read (.var varId)) le ls).2 ∧
      BuilderEffectRefinement module vt (lowerContextAt env.mod env.ctx env.impl) next start.eff
        (lowerExpr (.read (.var varId)) le ls).2 := by
    change BuilderRootWitness res vt (lowerContextAt env.mod env.ctx env.impl) next
        (recordReadValueRootRecipe (emitDef (.load address.1) le address.2).1 (.var varId) le
          (emitDef (.load address.1) le address.2).2).2 ∧
      BuilderEffectRefinement module vt (lowerContextAt env.mod env.ctx env.impl) next start.eff
        (recordReadValueRootRecipe (emitDef (.load address.1) le address.2).1 (.var varId) le
          (emitDef (.load address.1) le address.2).2).2
    rw [recordReadValueRootRecipe_run]
    simp only []
    split
    · rw [recordValueRootSource_run]
      exact ⟨⟨nextWitness.valueSize, nextWitness.instructions⟩, nextEffects⟩
    · exact ⟨nextWitness, nextEffects⟩
  refine ⟨next, recorded.1, recorded.2, ?_, slots.trans sameSlots⟩
  change rootsAt next.vals (emitDef (.load address.1) le address.2).1 = [.param varId]
  rw [roots]
  have value : (emitDef (.load address.1) le address.2).1 = address.2.vals.size := by
    rw [emitDef_run _ _ middleCurrent]
  rw [value]
  exact exactRoots



end Goose.Lower.Validation.SummaryPreservation

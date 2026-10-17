import Goose.Lower.Validation.SummaryPreservationContentSource
import Goose.Lower.Validation.SummaryPreservationEmitContent

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerExpr_content_read_source_witness {env : PEnv} {context : ContextId}
    {index : Nat} {param : Param} {localVar : LocalVar} {roots : List RootRef}
    {before after : RState} {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {upper : Prov} {ls : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId}
    {mu : Mutability} {element : Ty}
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[context]? = some env.ctx)
    (implLookup : env.mod.impls[env.ctx.impl]? = some env.impl)
    (parameter : env.impl.params[index]? = some param)
    (variableRow : env.impl.vars[param.var]? = some localVar)
    (reference : localVar.ty.isRefSlice = true)
    (source : rpExpr env (.read (.deref (.read (.var param.var)))) before = .ok (roots, after))
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) upper ls)
    (prior : BuilderEffectRefinement (lower env.mod) vt
      (lowerContextAt env.mod env.ctx env.impl) upper before.eff ls)
    (slotBound : param.var < le.slots.size)
    (slots : upper.slots = typedContextSlotUpper env.mod env.ctx env.impl)
    (addressType : vt[(lowerPlace (.var param.var) le ls).2.vals.size]? =
      some (some (.data localVar.ty)))
    (sliceType : vt[(lowerExpr (.read (.var param.var)) le ls).2.vals.size]? =
      some (some (.data (.slice mu element)))) :
    ∃ next : Prov,
      BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) next
        (lowerExpr (.read (.deref (.read (.var param.var)))) le ls).2 ∧
      BuilderEffectRefinement (lower env.mod) vt (lowerContextAt env.mod env.ctx env.impl) next after.eff
        (lowerExpr (.read (.deref (.read (.var param.var)))) le ls).2 ∧
      RootsRefine (lowerContextAt env.mod env.ctx env.impl)
        (rootsAt next.vals (lowerExpr (.read (.deref (.read (.var param.var)))) le ls).1) roots ∧
      next.slots = upper.slots := by
  obtain ⟨readAfter, placeSource⟩ := rpExpr_content_place_contract accepted contextLookup implLookup
    parameter variableRow reference source
  obtain ⟨middle, middleWitness, middleEffects, middleRoots, sameSlots⟩ :=
    lowerExpr_refSlice_address_source_witness symbols current blockBound witness prior slotBound
      variableRow placeSource reference slots addressType
  let address := lowerPlace (.var param.var) le ls
  let read := lowerExpr (.read (.var param.var)) le ls
  have readValue : read.1 = (emitDef (.load address.1) le address.2).1 := by
    simp [read, address, lowerExpr_read_var_after_address]
  have readCurrent : read.2.cur = (emitDef (.load address.1) le address.2).2.cur := by
    dsimp only [read]
    rw [lowerExpr_read_var_after_address]
    dsimp only [address]
    rw [recordReadValueRootRecipe_run]
    simp only []
    split
    · rw [recordValueRootSource_run]
    · rfl
  have readBlockCount : read.2.blocks.size = (emitDef (.load address.1) le address.2).2.blocks.size := by
    dsimp only [read]
    rw [lowerExpr_read_var_after_address]
    dsimp only [address]
    rw [recordReadValueRootRecipe_run]
    simp only []
    split
    · rw [recordValueRootSource_run]
    · rfl
  have readValueCount : read.2.vals.size = (emitDef (.load address.1) le address.2).2.vals.size := by
    dsimp only [read]
    rw [lowerExpr_read_var_after_address]
    dsimp only [address]
    rw [recordReadValueRootRecipe_run]
    simp only []
    split
    · rw [recordValueRootSource_run]
    · rfl
  have addressCurrent : address.2.cur = some block := by
    dsimp [address, lowerPlace]
    rw [emitDef_run _ _ current]
    exact current
  have addressBlockBound : block < address.2.blocks.size := by
    dsimp [address, lowerPlace]
    rw [emitDef_run _ _ current]
    simpa using blockBound
  have middleCurrent : read.2.cur = some block := by
    rw [readCurrent]
    rw [emitDef_run _ _ addressCurrent]
    exact addressCurrent
  have middleBlockBound : block < read.2.blocks.size := by
    rw [readBlockCount]
    rw [emitDef_run _ _ addressCurrent]
    simpa using addressBlockBound
  have valueBound : read.1 < read.2.vals.size := by
    rw [readValue, readValueCount]
    rw [emitDef_run _ _ addressCurrent]
    simp
  have middleSymbols := lowerExpr_read_var_symbols symbols current blockBound param.var slotBound
  have identity := ((validate_modOk env.mod accepted).impl env.ctx.impl env.impl implLookup).params
    index param parameter |>.1
  have actualRoots : rootsAt middle.vals read.1 = [.param index] := by
    exact middleRoots.trans (congrArg (fun variableId => [RootRef.param variableId]) identity)
  have place : rpPlace env (.deref (.read (.var param.var))) before =
      .ok ([.param index], readAfter) := placeSource
  obtain ⟨next, nextWitness, nextEffects, nextRoots, nextSlots⟩ :=
    emitDef_content_read_source_witness accepted contextLookup implLookup parameter variableRow reference
      place source middleSymbols middleCurrent middleBlockBound middleWitness middleEffects
      valueBound actualRoots sliceType
      (value := (emitDef (.load read.1) le read.2).1)
      (final := (emitDef (.load read.1) le read.2).2) rfl
  exact ⟨next, nextWitness, nextEffects, nextRoots, nextSlots.trans sameSlots⟩

end Goose.Lower.Validation.SummaryPreservation

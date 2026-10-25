import Goose.Lower.Validation.SummaryPreservationRefSliceAddresses
import Goose.Lower.Validation.SummaryPreservationContentReads

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem readRoots_refSlice_contents {env : PEnv} {varId : VarId} {localVar : LocalVar}
    {roots : List RootRef} {before after : RState}
    (variableRow : env.impl.vars[varId]? = some localVar)
    (reference : localVar.ty.isRefSlice = true)
    (source : readRoots env (.deref (.read (.var varId))) before = .ok (roots, after)) :
    env.cont varId = some roots := by
  have sliceVariable : env.isRefSliceVar varId = true := by
    simp [PEnv.isRefSliceVar, variableRow, reference]
  cases contents : env.cont varId with
  | none =>
    simp only [readRoots, sliceVariable, ite_true, contents] at source
    change Except.error _ = Except.ok _ at source
    cases source
  | some annotated =>
    have pair := (st_pure_ok _ _ _).mp (show (pure annotated : P (List RootRef)) before =
      .ok (roots, after) by simpa only [readRoots, sliceVariable, ite_true, contents] using source)
    have same : roots = annotated := congrArg Prod.fst pair
    simpa [same] using contents


theorem rpExpr_content_place_contract {env : PEnv} {context : ContextId} {index : Nat}
    {param : Param} {localVar : LocalVar} {roots : List RootRef} {initial after : RState}
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[context]? = some env.ctx)
    (implLookup : env.mod.impls[env.ctx.impl]? = some env.impl)
    (parameter : env.impl.params[index]? = some param)
    (variableRow : env.impl.vars[param.var]? = some localVar)
    (reference : localVar.ty.isRefSlice = true)
    (source : rpExpr env (.read (.deref (.read (.var param.var)))) initial = .ok (roots, after)) :
    ∃ before, rpExpr env (.read (.var param.var)) initial = .ok ([.param index], before) := by
  change (do
    let place ← rpPlace env (.deref (.read (.var param.var)))
    addReads place
    readRoots env (.deref (.read (.var param.var)))) initial = .ok (roots, after) at source
  obtain ⟨placeRoots, before, place, tail⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, afterReads, _, readSource⟩ := (st_bind_ok _ _ _ _).mp tail
  have contents := readRoots_refSlice_contents variableRow reference readSource
  have moduleOk := validate_modOk env.mod accepted
  obtain ⟨checkedImpl, lookup, checked⟩ := moduleOk.ctx context env.ctx contextLookup
  rw [implLookup] at lookup
  cases lookup
  have annotation := (checked.content param.var roots contents).2.1
  have identity := (moduleOk.impl env.ctx.impl env.impl implLookup).params index param parameter |>.1
  have sourceRoots := readRoots_variable_annotation checked.annotationShape variableRow
    (show readRoots env (.var param.var) initial = .ok (placeRoots, before) from place)
  change placeRoots = ((env.ctx.varRoots.find? (·.1 == param.var)).map (·.2)).getD [] at sourceRoots
  rw [annotation] at sourceRoots
  simp only [Option.getD_some, identity] at sourceRoots
  refine ⟨before, ?_⟩
  change rpExpr env (.read (.var param.var)) initial = .ok ([.param index], before)
  simpa only [sourceRoots, rpPlace] using place


theorem lowerExpr_read_var_after_address (varId : VarId) (le : LEnv) (ls : LS) :
    lowerExpr (.read (.var varId)) le ls =
      let loaded := emitDef (.load (lowerPlace (.var varId) le ls).1) le
        (lowerPlace (.var varId) le ls).2
      (loaded.1, (recordReadValueRootRecipe loaded.1 (.var varId) le loaded.2).2) := rfl


theorem lowerExpr_read_var_symbols {ls : LS} {le : LEnv} {scopeCount : Nat}
    {block : BlockId} (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (varId : VarId) (slotBound : varId < le.slots.size) :
    (lowerExpr (.read (.var varId)) le ls).2.SymbolWF le scopeCount := by
  let address := lowerPlace (.var varId) le ls
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
  have loadedSymbols : (emitDef (.load address.1) le address.2).2.SymbolWF le scopeCount := by
    rw [emitDef_run _ _ middleCurrent]
    apply LS.SymbolWF.emitDef middleSymbols middleCurrent middleBlockBound
    apply Inst.SymbolsWithin.def
    · simpa [Op.uses] using addressBound
    · simp [Op.origin]
    · simp [Op.SymbolRefsValid]
  rw [lowerExpr_read_var_after_address]
  change (recordReadValueRootRecipe (emitDef (.load address.1) le address.2).1 (.var varId) le
    (emitDef (.load address.1) le address.2).2).2.SymbolWF le scopeCount
  rw [recordReadValueRootRecipe_run]
  simp only []
  split
  · rw [recordValueRootSource_run]
    exact ⟨loadedSymbols.definitions, loadedSymbols.instructions⟩
  · exact loadedSymbols

end Goose.Lower.Validation.SummaryPreservation

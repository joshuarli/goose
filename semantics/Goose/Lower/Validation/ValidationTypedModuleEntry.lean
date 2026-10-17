import Goose.Lower.Validation.ValidationTypedModuleTables
import Goose.Lower.Finish

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem allocated_entry_retained (types : List VTy) (le : LEnv) {state : LS}
    (extension : (newBlock types le initState).2.Ext state) :
    ∃ block, (finishBlocks state.blocks)[0]? = some block ∧ block.params.map (·.2) = types := by
  let initial : BlockB := ⟨(paramIds types initState.vals).zip types, #[]⟩
  have row : (newBlock types le initState).2.blocks[0]? = some initial := by
    simp [newBlock_run_general, initState, initial]
  obtain ⟨block, located, params, _⟩ := extension.2 0 initial row
  refine ⟨⟨block.params, block.insts.toList⟩, ?_, ?_⟩
  · simp [finishBlocks, Array.getElem?_map, located]
  · rw [params]
    exact List.map_snd_zip (by simp [paramIds])

theorem lowerImpl_entry_types (module : Core.Module) (impl : Core.Impl) :
    ∃ block, (lowerImpl module impl).blocks[0]? = some block ∧
      block.params.map (·.2) = (lowerImpl module impl).params.map VTy.data := by
  let le := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun param => VTy.data (tyOfVar impl param.var)
  let allocated := newBlock types le initState
  let selected := setCur (some allocated.1.1) le allocated.2
  let pre : List (SlotId × ValueId × OriginId) := (impl.params.toList.zip allocated.1.2).map fun (param, value) =>
    (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
  let output := lowerBlock none pre false impl.body le selected.2
  have selectedExt : allocated.2.Ext selected.2 := .refl _
  have bodyExt := (advB_lowerBlock none pre false impl.body le selected.2 _ _ rfl).ext
  have finalExt := (advB_finishFunction impl output.1 le output.2 _ _ rfl).ext
  have retained := allocated_entry_retained types le (selectedExt.trans (bodyExt.trans finalExt))
  have same : types = (lowerImpl module impl).params.map VTy.data := by
    simp [types, lowerImpl, List.map_map, Function.comp_def]
  rw [same] at retained
  exact retained

theorem lowerContext_entry_types (module : Core.Module) (context : Context) (impl : Core.Impl) :
    ∃ block, (lowerContextAt module context impl).blocks[0]? = some block ∧
      block.params.map (·.2) = (lowerContextAt module context impl).params.map VTy.data :=
  lowerImpl_entry_types module impl

theorem lowerGlobal_entry_types (module : Core.Module) (global : Core.Global) :
    ∃ block, (lowerGlobal module global).init.blocks[0]? = some block ∧
      block.params.map (·.2) = (lowerGlobal module global).init.params.map VTy.data := by
  let le := lowerEnv module #[] [global.ty]
  let allocated := newBlock [] le initState
  let selected := setCur (some allocated.1.1) le allocated.2
  let output := lowerExpr global.init le selected.2
  have selectedExt : allocated.2.Ext selected.2 := .refl _
  have bodyExt := (advB_lowerExpr global.init le selected.2 _ _ rfl).ext
  have finalExt := (advB_emitTerm (.ret [output.1] (some global.org)) le output.2 _ _ rfl).ext
  exact allocated_entry_retained [] le (selectedExt.trans (bodyExt.trans finalExt))

end Goose.Lower.Validation

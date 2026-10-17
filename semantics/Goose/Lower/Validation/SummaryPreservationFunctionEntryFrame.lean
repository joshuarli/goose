import Goose.Lower.Validation.SummaryPreservationReplayFunctionFinish
import Goose.Lower.Validation.SummaryPreservationEntrySeeds
import Goose.Lower.Validation.CfgBuilderFunctions

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem finishFunction_ext (impl : Impl) (value : ValueId) (le : LEnv) (state : LS) :
    state.Ext (Goose.Lower.finishFunction impl value le state).2 := by
  cases current : state.cur with
  | none =>
    simpa only [Goose.Lower.finishFunction, bind_run, read_apply, isLive_none current,
      Bool.false_eq_true, ite_false, pure_run] using LS.Ext.refl state
  | some block =>
    by_cases sink : !impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges le.mod.noReturn
    · let fresh := newBlock [] le state
      let first := Goose.Lower.emitTerm (.br fresh.1.1 []) le fresh.2
      let selected := (Goose.Lower.setCur (some fresh.1.1) le first.2).2
      have firstExt := (advB_newBlock0 le state _ _ rfl).ext.trans
        (advB_emitTerm (.br fresh.1.1 []) le fresh.2 _ _ rfl).ext
      have secondExt : first.2.Ext selected := LS.Ext.refl first.2
      have finalExt := firstExt.trans (secondExt.trans
        (advB_emitTerm (.br fresh.1.1 []) le selected _ _ rfl).ext)
      have whole : Goose.Lower.finishFunction impl value le state =
          Goose.Lower.emitTerm (.br fresh.1.1 []) le selected := by
        simp only [Goose.Lower.finishFunction, bind_run, read_apply, isLive_run current,
          ite_true, sink, fresh, first, selected]
      rw [whole]
      exact finalExt
    · have whole : Goose.Lower.finishFunction impl value le state =
          Goose.Lower.emitTerm (.ret (if impl.body.value.isSome then [value] else []) none) le state := by
        simp only [Goose.Lower.finishFunction, bind_run, read_apply, isLive_run current,
          ite_true, sink, Bool.false_eq_true, ite_false]
      rw [whole]
      exact (advB_emitTerm (.ret (if impl.body.value.isSome then [value] else []) none) le state _ _ rfl).ext

theorem cfg_impl_entry_parameters (module : Core.Module) (impl : Impl) {ctx : Context} :
    ∀ block, (lowerContextAt module ctx impl).blocks[0]? = some block →
      block.params = (List.range impl.params.size).zip
        (impl.params.toList.map fun param => .data (tyOfVar impl param.var)) := by
  let le := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun param => VTy.data (tyOfVar impl param.var)
  let entry := entryReplayState types le
  let bindings : List (SlotId × ValueId × OriginId) := (impl.params.toList.zip (newBlock types le initState).1.2).map fun (param, value) =>
    (param.var, value, (impl.vars[param.var]?.map fun localVar : LocalVar => localVar.org).getD 0)
  let body := lowerBlock none bindings false impl.body le entry
  have whole : cfg_implState module impl = (Goose.Lower.finishFunction impl body.1 le body.2).2 := by
    simp only [cfg_implState, cfg_implAction, bind_run, setCur_run, body, bindings,
      entry, entryReplayState, types, le]
  have advance := (advB_lowerBlock none bindings false impl.body le entry _ _ rfl).ext.trans
    (finishFunction_ext impl body.1 le body.2)
  let initialBlock : BlockB := {params := (List.range impl.params.size).zip types, insts := #[]}
  have initialRow : entry.blocks[0]? = some initialBlock := by
    simp [entry, entryReplayState, newBlock_run_general, initState, initialBlock, types, paramIds]
  obtain ⟨finished, finalRow, same, _⟩ := advance.2 0 initialBlock initialRow
  intro block row
  rw [cfg_context_blocks, whole] at row
  simp only [finishBlocks, Array.getElem?_map, finalRow, Option.map_some, Option.some.injEq] at row
  cases row
  exact same

theorem cfg_impl_entry_type_prefix (module : Core.Module) (impl : Impl) :
    TypePrefix (entryReplayState (impl.params.toList.map fun param => .data (tyOfVar impl param.var))
      (lowerEnv module impl.vars impl.results.toList)) (cfg_implState module impl) := by
  let le := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun param => VTy.data (tyOfVar impl param.var)
  let entry := entryReplayState types le
  let bindings : List (SlotId × ValueId × OriginId) :=
    (impl.params.toList.zip (newBlock types le initState).1.2).map fun (param, value) =>
      (param.var, value, (impl.vars[param.var]?.map fun localVar : LocalVar => localVar.org).getD 0)
  let body := lowerBlock none bindings false impl.body le entry
  have whole : cfg_implState module impl = (Goose.Lower.finishFunction impl body.1 le body.2).2 := by
    simp only [cfg_implState, cfg_implAction, bind_run, setCur_run, body, bindings,
      entry, entryReplayState, types, le]
  rw [whole]
  exact (types_lowerBlock none bindings false impl.body le entry _ _ rfl).trans
    (ReplayBuilder.types_finishFunction impl body.1 le body.2 _ _ rfl)

theorem entryReplayState_parameter_type {types : List VTy} {index : Nat} {type : VTy}
    (le : LEnv) (row : types[index]? = some type) :
    (entryReplayState types le).vals[index]? = some (some type) := by
  change (pushParamTypes types #[])[index]? = some (some type)
  simpa only [Array.size_empty, Nat.zero_add, row, Option.map_some] using
    pushParamTypes_lookup types #[] index

#print axioms cfg_impl_entry_type_prefix
#print axioms entryReplayState_parameter_type

#print axioms finishFunction_ext
#print axioms cfg_impl_entry_parameters

end Goose.Lower.Validation.SummaryPreservation

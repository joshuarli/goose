import Goose.Lower.Validation.EmittedMetadataSourceContracts
import Goose.Core.Sound.Module

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerImpl_entry_pretyped_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {impl : Core.Impl} {index : ImplId}
    (implAt : module.impls[index]? = some impl) :
    let le := lowerEnv module impl.vars impl.results.toList
    let types := impl.params.toList.map fun param => VTy.data (tyOfVar impl param.var)
    let allocated := newBlock types le initState
    let selected := setCur (some allocated.1.1) le allocated.2
    let pre := (impl.params.toList.zip allocated.1.2).map fun (param, value) =>
      (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
    EmittedPreTyped le selected.2 pre := by
  dsimp only
  let le := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun param => VTy.data (tyOfVar impl param.var)
  let allocated := newBlock types le initState
  let selected := setCur (some allocated.1.1) le allocated.2
  intro slot value origin member
  obtain ⟨⟨param, parameterValue⟩, paired, same⟩ := List.mem_map.mp member
  cases same
  obtain ⟨position, pairedAt⟩ := List.mem_iff_getElem?.mp paired
  obtain ⟨paramAt, valueAt⟩ := List.getElem?_zip_eq_some.mp pairedAt
  have paramRow : impl.params[position]? = some param := by simpa only [Array.getElem?_toList] using paramAt
  obtain ⟨variableEq, localVar, localRow, scope, parameterType⟩ :=
    ((validate_modOk module accepted).impl index impl implAt).params position param paramRow
  have variableRow : impl.vars[param.var]? = some localVar := by simpa only [variableEq] using localRow
  have slotAt : le.slots[param.var]? = some ⟨localVar.ty, localVar.kind, localVar.scope, param.var⟩ := by
    simp [le, lowerEnv, Array.getElem?_mapIdx, variableRow]
  have typeAt : types[position]? = some (.data localVar.ty) := by
    simp [types, List.getElem?_map, paramAt, tyOfVar, variableRow]
  have positionBound : position < types.length := (List.getElem?_eq_some_iff.mp typeAt).1
  dsimp only [types] at positionBound
  have identity : initState.vals.size + position = parameterValue := by
    simpa only [allocated, newBlock_run_general, paramIds, List.getElem?_map,
      List.getElem?_range positionBound, Option.map_some, Option.some.injEq] using valueAt
  have recorded := newBlock_parameter_types types le initState position
  rw [typeAt] at recorded
  refine ⟨_, slotAt, ?_⟩
  change allocated.2.vals[parameterValue]? = some (some (.data localVar.ty))
  rw [← identity]
  exact recorded

end Goose.Lower.Validation

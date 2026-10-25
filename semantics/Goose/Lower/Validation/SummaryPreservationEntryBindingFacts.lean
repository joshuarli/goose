import Goose.Lower.Validation.SummaryPreservationEntryBindings
import Goose.Lower.Validation.SummaryPreservationReplayEntry
import Goose.Lower.GeneratedBuilder

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def contextEntryBindings (impl : Impl) (le : LEnv) : List (SlotId × ValueId × OriginId) :=
  (impl.params.toList.zip (newBlock (impl.params.toList.map fun p => .data (tyOfVar impl p.var)) le initState).1.2).map
    fun (param, value) => (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)

theorem contextEntryBindings_metadata {module : Core.Module} {impl : Impl} {index : ImplId}
    (le : LEnv) (accepted : Core.validate module = .ok ()) (row : module.impls[index]? = some impl) :
    ∀ binding ∈ contextEntryBindings impl le,
      binding.1 < impl.vars.size ∧ binding.2.2 < module.origins.size := by
  intro binding member
  obtain ⟨⟨param, value⟩, paired, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, localVar, _, identity, _, variableRow, originBound⟩ := entry_parameter_pair le accepted row paired
  constructor
  · change param.var < impl.vars.size
    rw [identity]
    exact (Array.getElem?_eq_some_iff.mp variableRow).1
  · simpa only [identity, variableRow, Option.map_some, Option.getD_some] using originBound

theorem contextEntryBindings_values {module : Core.Module} {impl : Impl} {index : ImplId}
    (le : LEnv) (accepted : Core.validate module = .ok ()) (row : module.impls[index]? = some impl) :
    ∀ binding ∈ contextEntryBindings impl le, binding.2.1 <
      (entryReplayState (impl.params.toList.map fun p => .data (tyOfVar impl p.var)) le).vals.size := by
  intro binding member
  obtain ⟨⟨param, value⟩, paired, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, localVar, parameterRow, _, same, _, _⟩ := entry_parameter_pair le accepted row paired
  rw [same, entryReplayState_values_size]
  simpa only [List.length_map, Array.length_toList] using (Array.getElem?_eq_some_iff.mp parameterRow).1

theorem contextEntryBindings_roots {module : Core.Module} {ctx : Context} {impl : Impl} {index : ImplId}
    (le : LEnv) (accepted : Core.validate module = .ok ()) (row : module.impls[index]? = some impl)
    (checked : CtxOk module impl ctx) :
    ∀ binding ∈ contextEntryBindings impl le, ∀ root ∈ rootsAt
      (entryRootValues (impl.params.toList.map fun p => .data (tyOfVar impl p.var))) binding.2.1,
      root ∈ rootsAt (typedContextSlotUpper module ctx impl) binding.1 := by
  intro binding member
  obtain ⟨⟨param, value⟩, paired, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, localVar, parameterRow, identity, same, variableRow, _⟩ := entry_parameter_pair le accepted row paired
  rw [same]
  exact entry_parameter_roots_within_slots checked parameterRow identity variableRow

theorem entryReplayState_generated (types : List VTy) (le : LEnv) :
    GeneratedBuilderState (entryReplayState types le) := by
  have allocated := GeneratedBuilderState.initState.newBlock types (env := le) rfl
  exact allocated.setCur (some (newBlock types le initState).1.1) (by
    intro block same
    cases Option.some.inj same
    simp [newBlock_run_general]) (env := le) rfl

theorem lowerBlock_value_want (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (body : Core.Block) : lowerBlock loop pre body.value.isSome body = lowerBlock loop pre false body := by
  cases body with
  | mk scope statements value => cases value <;> rfl

end Goose.Lower.Validation.SummaryPreservation

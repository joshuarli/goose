import Goose.Proofs.ConstructionRootedBackingPrefixes
import Goose.Proofs.ConstructionPackedCountInitialization
import Goose.Proofs.ConstructionFixedElementGeometry

set_option Elab.async false

namespace Goose.Proofs.ConstructionRepresentation
open Goose.Construct

theorem finishDestination_varrByte_backing (layoutEnv : LayoutEnv) (state : ExecutionState)
    (after : ConstructionState) (id : Nat) (destination : PendingDestination)
    (storage : ReceivingStorage) (count : Nat)
    (present : state.construction.destinations[id]? = some destination)
    (stored : state.construction.storage[destination.storage]? = some storage)
    (opened : destination.progress = .open count) (layout : destination.layout = .packed)
    (request : destination.capability.request = .value)
    (logicalType : destination.capability.logicalType = .varr (.int .u8))
    (bounded : destination.capability.start + 4 + count ≤ storage.bytes.size)
    (fits : count < 2 ^ 32)
    (executed : finishDestination id state.construction = .ok () after) :
    ∃ value current,
      after.storage[destination.storage]? = some current ∧
      storedDestination id { state with construction := after } =
        .ok value { state with construction := after } ∧
      StoredValueBacking layoutEnv { state with construction := after } value ∧
      packedEnd (count + 2) layoutEnv (.varr (.int .u8)) current.bytes destination.capability.start =
        .ok (destination.capability.start + 4 + count) := by
  obtain ⟨current, currentFound, counted, size, completed⟩ :=
    finishDestination_packed_count state.construction after id destination storage count
      present stored opened layout request (by omega) fits executed
  have measured : elementsEnd (count + 1) layoutEnv (.int .u8) count current.bytes
      (destination.capability.start + 4) = .ok (destination.capability.start + 4 + count) := by
    have bound : (destination.capability.start + 4) + count * 1 ≤ current.bytes.size := by
      rw [size]
      simpa only [Nat.mul_one] using bounded
    simpa only [Nat.mul_one] using elementsEnd_fixed layoutEnv current.bytes (.int .u8) 1 rfl count
      (destination.capability.start + 4) bound
  let value : StoredValue :=
    ⟨destination.storage, destination.capability.start, .varr (.int .u8), count, some id, none, [], count⟩
  refine ⟨value, current, currentFound, ?_, ?_, ?_⟩
  · simp only [storedDestination, getDestination, EvalM.get, bind, completed, progressCount,
      pure, logicalType, value]
    rfl
  · refine .named id current { destination with progress := .built count } count currentFound rfl completed
      rfl logicalType.symm rfl rfl (.int .u8) rfl ?_
    have interval : SampledRunBacking layoutEnv current.bytes
        ⟨destination.capability.start + 4, count, .int .u8⟩ := by
      refine ⟨count + 1, destination.capability.start + 4 + count, measured, ?_, ?_⟩
      · change destination.capability.start + 4 ≤ destination.capability.start + 4 + count
        omega
      · rw [size]
        exact bounded
    simpa [storedWrittenRun, value, layout, request] using interval
  · rw [packedEnd]
    simp only [fixedByteSize?, counted, bind, Except.bind]
    exact measured

#print axioms finishDestination_varrByte_backing

end Goose.Proofs.ConstructionRepresentation

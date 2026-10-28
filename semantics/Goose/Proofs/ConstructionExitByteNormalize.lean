import Goose.Proofs.ExitExecutionLandedChannels

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem receiver_destination_writable (state : ConstructionState) (id : Nat)
    (row : PendingDestination) (present : state.destinations[id]? = some row) (receiver : row.use = .receiver) :
    destinationCanWrite state id = true := by
  simp only [destinationCanWrite_result, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  cases size : state.destinations.size with
  | zero =>
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    omega
  | succ n =>
    simp [size, List.range'_succ, present, receiver, Id.run]
    rfl

theorem byte_receiver_finishChannel (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (state : ExecutionState) (id count : Nat) (row : PendingDestination)
    (present : state.construction.destinations[id]? = some row)
    (built : row.progress = .built count) (receiver : row.use = .receiver)
    (adaptation : row.adaptation = none)
    (physical : row.capability.layout = .varr (.int .u8))
    (logical : row.capability.logicalType = .varr (.int .u8)) :
    finishChannel layout origin (.completed id) (.varr (.int .u8)) state = .ok () state := by
  have valid : NormalizedCompletedCarrier state (.varr (.int .u8)) id :=
    ⟨row, present, ⟨count, built⟩, receiver_destination_writable state.construction id row present receiver,
      adaptation, by simp only [physical, Bool.not_true, Bool.and_false], logical, rfl⟩
  exact valid.finishChannel state (.varr (.int .u8)) id layout origin

#print axioms byte_receiver_finishChannel
#print axioms receiver_destination_writable

end Goose.Proofs.ExitExecution

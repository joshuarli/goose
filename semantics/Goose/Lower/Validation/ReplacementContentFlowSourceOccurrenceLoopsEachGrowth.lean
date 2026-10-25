import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLoopsEachPrelude

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

theorem occurrenceEachPrelude_values (regrow : Bool) (owner : Option ValueId) (view : ValueId)
    (body : Nat → BlockId → BlockId → ValueId → B ValueId)
    (bodyAdvance : ∀ depth header exit counter, AdvB (body depth header exit counter))
    (le : LEnv) (initial : LS) :
    initial.vals.size ≤ (nativeEachPrelude regrow owner view body le initial).2.vals.size := by
  have advance : AdvB (nativeEachPrelude regrow owner view body) := by
    unfold nativeEachPrelude
    apply AdvB.bind (advB_eachSampled regrow view)
    intro sampled
    apply AdvB.bind (advB_emitDef (.constInt .i64 0))
    intro first
    apply advB_header1 (tail := fun header counter =>
      lowerEach regrow owner sampled header counter
        (fun depth exit => body depth header exit counter)) (.data (.int .i64)) first
    intro header counter
    exact advB_lowerEach regrow owner sampled header counter
      (fun depth exit => bodyAdvance depth header exit counter)
  exact (advance le initial
    (nativeEachPrelude regrow owner view body le initial).1
    (nativeEachPrelude regrow owner view body le initial).2
    (Prod.eta (nativeEachPrelude regrow owner view body le initial)).symm).vals

#print axioms occurrenceEachPrelude_values

end Goose.Lower.Validation.ReplacementContentFlowSource

import Goose.Lower.Validation.SummaryPreservationStoppedGraph

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem stopped_coerceTo (target : Ty) (value : ValueId) (origin : OriginId) :
    StoppedGraph (coerceTo target value origin) := by
  unfold coerceTo
  refine StoppedGraph.bind (stopped_valTy value) fun source => ?_
  split
  · exact stopped_emitDef _
  · exact StoppedGraph.bind (stopped_emitDef _) fun _ => stopped_emitDef _
  · exact StoppedGraph.pure _

theorem stopped_coerceSlot (slot : SlotId) (value : ValueId) (origin : OriginId) :
    StoppedGraph (coerceSlot slot value origin) := by
  unfold coerceSlot
  refine StoppedGraph.bind stopped_read fun le => ?_
  cases le.slots[slot]? with
  | none => exact StoppedGraph.pure _
  | some destination => exact stopped_coerceTo _ _ _

end Goose.Lower.Validation.SummaryPreservation

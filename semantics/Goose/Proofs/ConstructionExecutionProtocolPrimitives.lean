import Goose.Proofs.ConstructionExecutionProtocolDestination

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

private theorem recordCopy_emit_preserves (source : CopySource) (id : DestinationId)
    (state : ConstructionState) (destination : PendingDestination) (count : Nat)
    (present : state.destinations[id]? = some destination)
    (progress : destination.progress = .open count) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with events := state.events ++ [.copy source id] } := by
  refine ⟨?_, valid.2.1, valid.2.2.1, valid.2.2.2⟩
  apply destinationTraceProtocol_emit state id destination [.copy source id] present
  · intro index different
    simp [destinationObservations, observeDestination, Ne.symm different]
  · intro phase matched
    exact ⟨phase, copy_destination_trace_transition id source destination count progress phase matched,
      matched⟩
  · exact valid.1

theorem recordCopy_destination_lifecycle_invariant (source : CopySource) (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (recordCopy source id state).finalState := by
  simp only [recordCopy, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact valid
      | true =>
          simp only [allowed]
          cases progress : destination.progress <;> try simp only [progress] <;> try exact valid
          case «open» count =>
            have emitted := recordCopy_emit_preserves source id state destination count present progress valid
            cases source with
            | storage sourceId path =>
                simp only [lookupStorage_result, bind]
                cases state.storage[sourceId]? <;>
                  simp only [bind, pure, emit_result, ConstructionResult.finalState]
                · exact valid
                · exact emitted
            | «repeat» sourceId =>
                simp only [lookupDestination_result, bind]
                cases found : state.destinations[sourceId]? with
                | none => exact valid
                | some sourceDestination =>
                    simp only [found]
                    cases progress : sourceDestination.progress <;>
                      simp only [progress, bind, pure, emit_result, ConstructionResult.finalState] <;>
                      first | exact valid | exact emitted

private theorem stageDestination_lifecycle_parts (id : DestinationId) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    DestinationTraceProtocol (stageDestination id state).finalState ∧
      DestinationStorageReferencesValid (stageDestination id state).finalState ∧
      DestinationOwnersOrdered (stageDestination id state).finalState := by
  simp only [stageDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact ⟨valid.1, valid.2.2.1, valid.2.2.2⟩
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact ⟨valid.1, valid.2.2.1, valid.2.2.2⟩
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          cases progress : destination.progress <;> try simp only [progress] <;>
            try exact ⟨valid.1, valid.2.2.1, valid.2.2.2⟩
          case «open» count =>
            cases count <;> try exact ⟨valid.1, valid.2.2.1, valid.2.2.2⟩
            case zero =>
              cases layout : destination.layout <;> try simp only [layout] <;>
                try exact ⟨valid.1, valid.2.2.1, valid.2.2.2⟩
              case limited capacity slotBytes =>
                cases backing : destination.backing <;> try simp only [backing] <;>
                  try exact ⟨valid.1, valid.2.2.1, valid.2.2.2⟩
                case direct receiver =>
                  cases known : destination.knownCount <;> try simp only [known] <;>
                    try exact ⟨valid.1, valid.2.2.1, valid.2.2.2⟩
                  case none =>
                    cases use : destination.use <;> try simp only [use] <;>
                      try exact ⟨valid.1, valid.2.2.1, valid.2.2.2⟩
                    case receiver =>
                      simp only [reserveStorage, ConstructionM.get, ConstructionM.set, bind,
                        pure, replaceDestination_result, inside, ↓reduceIte, emit_result,
                        ConstructionResult.finalState]
                      refine ⟨?_, ?_, ?_⟩
                      · exact destinationTraceProtocol_replace state id destination _ [.stage id]
                          present (by
                            intro index different
                            simp [destinationObservations, observeDestination, Ne.symm different])
                          (by
                            intro phase matched
                            simpa only [progress, layout, known, use] using
                              stage_destination_trace_transition id receiver state.storage.size
                                destination progress backing phase matched) valid.1
                      · apply destinationStorageReferences_replace state id _
                            (state.storage.push ⟨ByteArray.empty, 0⟩)
                        · simp
                        · simp [PendingDestination.storage, DestinationBacking.writeStorage]
                        · have references := valid.2.2.1 id destination present
                          simpa only [Array.size_push, backing,
                            DestinationBacking.receiverStorage] using Nat.lt_succ_of_lt references.2
                        · exact valid.2.2.1
                      · exact destinationOwnersOrdered_replace state id destination _ present
                          (by simp only [use]) valid.2.2.2

theorem stageDestination_destination_lifecycle_invariant (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (stageDestination id state).finalState := by
  have parts := stageDestination_lifecycle_parts id state valid
  exact ⟨parts.1, stageDestination_destination_capabilities id state valid.2.1,
    parts.2.1, parts.2.2⟩

end Goose.Proofs.ConstructionExecutionProtocol

import Goose.Proofs.ConstructionExecutionOwnershipSourceMutations

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

local syntax "ownership_source_write_split_if" : tactic
elab_rules : tactic
  | `(tactic| ownership_source_write_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no ownership write condition to split"
      return [yes.mvarId, no.mvarId]

set_option maxHeartbeats 800000 in
theorem writeElement_ownership_source (id : DestinationId) (bytes : ByteArray)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    OwnershipSourceExtension state (writeElement id bytes state).finalState := by
  simp only [writeElement, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have bound := (valid.2.2.1 id destination present).1
          cases progress : destination.progress <;> (try simp only [progress]) <;> try exact .refl state
          case «open» count =>
            have committed : ∀ storage : ReceivingStorage,
                OwnershipSourceExtension state { state with
                  storage := state.storage.set! destination.storage storage
                  destinations := state.destinations.set! id { destination with progress := .open (count + 1), writeEnd := destination.writeEnd + bytes.size },
                  events := state.events ++ [.write id count] } := by
              intro storage
              refine ownershipSourceExtension_replace state id destination _ present ?_ ?_
              · rfl
              · cases use : destination.use <;> simp [OwnershipLinkBacking, use]
            cases stored : state.storage[destination.storage]? with
            | none => simp only [lookupStorage_result, stored, bind]; exact .refl state
            | some storage =>
                simp only [lookupStorage_result, stored, bind]
                ownership_source_write_split_if
                · exact .refl state
                · try simp only [pure, bind, ConstructionM.fail, ConstructionResult.finalState]
                  cases layout : (destination.adaptation.map (·.layout)).getD destination.layout <;>
                    simp only [layout]
                  all_goals
                    repeat' first
                      | simp only [pure, bind, ConstructionM.fail, ConstructionResult.finalState]
                      | ownership_source_write_split_if
                    all_goals try exact .refl state
                    all_goals
                      cases use : destination.use <;> simp only [use]
                      all_goals
                        try solve | repeat' first
                            | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                ConstructionM.fail, emit_result, ConstructionResult.finalState]
                            | ownership_source_write_split_if
                            | exact .refl state
                            | exact committed _
                      case child parentId =>
                        cases parentFound : state.destinations[parentId]? <;>
                          simp only [lookupDestination_result, parentFound, bind]
                        · repeat' first
                            | simp_all only [↓reduceIte, pure, bind, ConstructionM.fail, ConstructionResult.finalState]
                            | ownership_source_write_split_if
                            | exact .refl state
                        · rename_i parent
                          cases parentLayout : parent.layout <;> (try simp only [parentLayout])
                          all_goals
                            try solve | repeat' first
                                | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                    replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                    ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                | ownership_source_write_split_if
                                | exact .refl state
                                | exact committed _
                          case limited capacity slotBytes =>
                            cases parentProgress : parent.progress <;> (try simp only [parentProgress])
                            all_goals
                              try solve | repeat' first
                                | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                    replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                    ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                | ownership_source_write_split_if
                                | exact .refl state
                                | exact committed _
                            case suspended parentCount child =>
                              cases parentBacking : parent.backing <;> (try simp only [parentBacking])
                              all_goals
                                try solve | repeat' first
                                  | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                      replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                      ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                  | ownership_source_write_split_if
                                  | exact .refl state
                                  | exact committed _
                              case direct parentStorage =>
                                cases backing : destination.backing <;> (try simp only [backing])
                                all_goals
                                  repeat' first
                                    | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                        replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                        ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                    | ownership_source_write_split_if
                                    | exact .refl state
                                    | exact committed _

end Goose.Proofs.ConstructionExecutionOwnership

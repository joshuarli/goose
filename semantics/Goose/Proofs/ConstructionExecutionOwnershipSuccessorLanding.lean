import Goose.Proofs.ConstructionExecutionOwnershipSuccessors
import Goose.Proofs.ConstructionExecutionProtocolExitFrames

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

theorem exitLandingAnchor_chain_bounds (fuel selected storage : Nat) (receiving : Option DestinationId)
    (state after : ConstructionState) (anchor : DestinationId) (destination : PendingDestination)
    (chain : List DestinationId)
    (landed : exitLandingAnchor fuel selected storage receiving state = .ok (anchor, destination, chain) after) :
    ∀ id ∈ chain, id < selected := by
  have unchanged : after = state := by
    have frame := exitLandingAnchor_finalState fuel selected storage receiving state
    simpa only [landed, ConstructionResult.finalState] using frame
  subst after
  induction fuel generalizing selected anchor destination chain with
  | zero => simp [exitLandingAnchor, ConstructionM.fail] at landed
  | succ fuel ih =>
      simp only [exitLandingAnchor, lookupDestination_result, ConstructionM.get, ConstructionM.fail, bind, pure] at landed
      cases present : state.destinations[selected]? with
      | none => simp only [present] at landed; contradiction
      | some replacement =>
          simp only [present] at landed
          cases use : replacement.use <;> simp only [use, bind, pure, ConstructionM.fail] at landed <;> try contradiction
          case replacement old =>
            cases oldPresent : state.destinations[old]? with
            | none => simp only [oldPresent] at landed; contradiction
            | some superseded =>
                simp only [oldPresent] at landed
                cases malformed : (superseded.storage != storage || decide (old ≥ selected)) with
                | true => simp only [malformed, ↓reduceIte] at landed; contradiction
                | false =>
                    simp only [malformed, Bool.false_eq_true, ↓reduceIte] at landed
                    have earlier : old < selected := by
                      have bound := (Bool.or_eq_false_iff.mp malformed).2
                      simp only [decide_eq_false_iff_not, Nat.not_le] at bound
                      exact bound
                    cases progress : superseded.progress <;> simp only [progress] at landed <;> try contradiction
                    all_goals
                      try
                        rename_i count expected
                        cases mismatch : (expected != selected) <;>
                          simp only [mismatch, Bool.false_eq_true, ↓reduceIte] at landed <;> try contradiction
                    all_goals
                      cases boundary : (receiving == some old) <;>
                        simp only [boundary, Bool.false_eq_true, ↓reduceIte] at landed
                      · cases nextUse : superseded.use <;> simp only [nextUse] at landed
                        all_goals
                          try
                            cases hasBoundary : receiving.isSome <;>
                              simp only [hasBoundary, Bool.false_eq_true, ↓reduceIte, ConstructionM.fail] at landed <;>
                              try contradiction
                        all_goals try (cases landed; intro id member; simp only [List.mem_singleton] at member; simpa only [member] using earlier)
                        all_goals
                          cases recursive : exitLandingAnchor fuel old storage receiving state with
                          | fault reason final => simp only [recursive] at landed; contradiction
                          | ok value final =>
                              rcases value with ⟨root, row, rest⟩
                              have unchanged := exitLandingAnchor_finalState fuel old storage receiving state
                              simp only [recursive, ConstructionResult.finalState] at unchanged
                              subst final
                              have found := ih old root row rest recursive
                              simp only [recursive] at landed
                              cases landed
                              intro id member
                              rcases List.mem_cons.mp member with same | member
                              · simpa only [same] using earlier
                              · exact Nat.lt_trans (found id member) earlier
                      · cases landed
                        intro id member
                        simp only [List.mem_singleton] at member
                        simpa only [member] using earlier


theorem destinationSuccessorsValid_extension (before after : ConstructionState)
    (valid : DestinationSuccessorsValid before)
    (successors : after.destinationSuccessors = before.destinationSuccessors)
    (allocated : before.destinations.size ≤ after.destinations.size) : DestinationSuccessorsValid after := by
  intro id next present
  rw [successors] at present
  have bounds := valid id next present
  exact ⟨bounds.1, Nat.lt_of_lt_of_le bounds.2 allocated⟩

theorem destinationSuccessorsValid_prepend (state : ConstructionState)
    (replacement : DestinationId) (chain : List DestinationId)
    (valid : DestinationSuccessorsValid state) (inside : replacement < state.destinations.size)
    (earlier : ∀ id ∈ chain, id < replacement) :
    DestinationSuccessorsValid { state with destinationSuccessors := chain.map (fun id => (id, replacement)) ++ state.destinationSuccessors } := by
  intro id next present
  induction chain with
  | nil => exact valid id next present
  | cons first rest ih =>
      simp only [List.map_cons, List.cons_append, List.lookup_cons] at present
      cases same : (id == first) with
      | false =>
          simp only [same] at present
          exact ih (fun other member => earlier other (List.mem_cons_of_mem _ member)) present
      | true =>
          simp only [same, Option.some.injEq] at present
          subst next
          have equal : id = first := by simpa using same
          subst id
          exact ⟨earlier first (List.mem_cons_self), inside⟩

end Goose.Proofs.ConstructionExecutionOwnership

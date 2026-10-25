import Goose.Proofs.ConstructionExecutionProtocolExitFrames

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

theorem exitLandingAnchor_success (fuel selected storage : Nat) (receiving : Option DestinationId)
    (state after : ConstructionState) (anchor : DestinationId) (destination : PendingDestination)
    (chain : List DestinationId)
    (landed : exitLandingAnchor fuel selected storage receiving state = .ok (anchor, destination, chain) after) :
    after = state ∧ anchor < selected ∧ state.destinations[anchor]? = some destination := by
  have unchanged : after = state := by
    have frame := exitLandingAnchor_finalState fuel selected storage receiving state
    simpa only [landed, ConstructionResult.finalState] using frame
  subst after
  refine ⟨rfl, ?_⟩
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
                        all_goals try (cases landed; exact ⟨earlier, oldPresent⟩)
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
                              exact ⟨Nat.lt_trans found.1 earlier, found.2⟩
                      · cases landed; exact ⟨earlier, oldPresent⟩

end Goose.Proofs.ConstructionExecutionProtocol

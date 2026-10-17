import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsCleanupAncestry
import Goose.Proofs.ConstructionExecutionProtocolLandingAnchor

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

theorem exitLandingAnchor_replacement_path (fuel selected storage : Nat) (receiving : Option DestinationId)
    (state after : ConstructionState) (anchor : DestinationId) (destination : PendingDestination)
    (chain : List DestinationId)
    (landed : exitLandingAnchor fuel selected storage receiving state = .ok (anchor, destination, chain) after) :
    OwnershipReplacementPath state.destinations anchor selected := by
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
                        all_goals try (cases landed; exact .step _ _ _ replacement present use (.refl _))
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
                              exact .step _ _ _ replacement present use found
                      · cases landed; exact .step _ _ _ replacement present use (.refl _)


theorem OwnershipReplacementPath.supported {state : ConstructionState} {ancestor id : DestinationId}
    (path : OwnershipReplacementPath state.destinations ancestor id) :
    ReplacementSupported state id → ReplacementSupported state ancestor := by
  induction path with
  | refl => exact fun supported => supported
  | step id parent ancestor row present use path ih =>
      intro supported
      exact ih (.parent id parent row present use supported)

theorem OwnershipReplacementPath.backing {state : ConstructionState}
    (authority : SupportedReplacementAuthority state) {ancestor id : DestinationId}
    (path : OwnershipReplacementPath state.destinations ancestor id) :
    ∀ (rootRow leafRow : PendingDestination), state.destinations[ancestor]? = some rootRow →
      state.destinations[id]? = some leafRow → ReplacementSupported state id → leafRow.backing = rootRow.backing := by
  induction path with
  | refl id =>
      intro rootRow leafRow rootPresent leafPresent supported
      cases Option.some.inj (rootPresent.symm.trans leafPresent)
      rfl
  | step id parent ancestor row present use path ih =>
      intro rootRow leafRow rootPresent leafPresent supported
      have equal := Option.some.inj (leafPresent.symm.trans present)
      subst leafRow
      obtain ⟨owner, ownerPresent, backing, phase⟩ := authority id parent row present use supported
      exact backing.trans (ih rootRow owner rootPresent ownerPresent (.parent id parent row present use supported))

end Goose.Proofs.ConstructionExecutionOwnership

import Goose.Proofs.ExitExecutionCompletedObservations
import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsCleanupAncestry

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionOwnership

private theorem replacementPath_tail (state : ConstructionState) (receiver selected old : Nat)
    (row : PendingDestination) (present : state.destinations[selected]? = some row)
    (use : row.use = .replacement old) (path : OwnershipReplacementPath state.destinations receiver selected)
    (different : receiver ≠ selected) : OwnershipReplacementPath state.destinations receiver old := by
  cases path with
  | refl => exact False.elim (different rfl)
  | step selected parent receiver actual found actualUse tail =>
    have same := Option.some.inj (found.symm.trans present)
    subst actual
    have parentSame := DestinationUse.replacement.inj (actualUse.symm.trans use)
    subst parent
    exact tail

private theorem replacementPath_terminal (state : ConstructionState) (receiver selected : Nat)
    (row : PendingDestination) (present : state.destinations[selected]? = some row)
    (terminal : ∀ parent, row.use ≠ .replacement parent)
    (path : OwnershipReplacementPath state.destinations receiver selected) : receiver = selected := by
  cases path with
  | refl => rfl
  | step selected parent receiver actual found actualUse tail =>
    have same := Option.some.inj (found.symm.trans present)
    subst actual
    exact False.elim (terminal parent actualUse)

theorem exitLandingAnchor_supported (fuel : Nat) (state : ConstructionState)
    (ordered : DestinationOwnersOrdered state) (authority : SupportedReplacementAuthority state)
    (selected old : Nat) (row : PendingDestination) (receiving : Option Nat)
    (present : state.destinations[selected]? = some row) (use : row.use = .replacement old)
    (supported : ReplacementSupported state selected) (budget : selected < fuel)
    (boundary : ∀ receiver, receiving = some receiver → receiver < selected ∧
      OwnershipReplacementPath state.destinations receiver selected) :
    ∃ anchor destination chain,
      exitLandingAnchor fuel selected row.storage receiving state = .ok (anchor, destination, chain) state ∧
      state.destinations[anchor]? = some destination ∧ destination.backing = row.backing ∧
      ReplacementSupported state anchor ∧
      (∀ receiver, receiving = some receiver → anchor = receiver) ∧
      (receiving = none → ∀ parent, destination.use ≠ .replacement parent) := by
  induction fuel generalizing selected old row with
  | zero => omega
  | succ fuel ih =>
    obtain ⟨owner, ownerFound, sameBacking, progress⟩ := authority selected old row present use supported
    have ownerEarlier : old < selected := by simpa only [use] using ordered selected row present
    have oldSupported := ReplacementSupported.parent selected old row present use supported
    have storageSame : owner.storage = row.storage := congrArg DestinationBacking.writeStorage sameBacking.symm
    have shape : (owner.storage != row.storage || decide (old ≥ selected)) = false := by
      simp only [storageSame, bne_self_eq_false, Bool.false_or, decide_eq_false_iff_not]
      omega
    have dispatch : exitLandingAnchor (fuel + 1) selected row.storage receiving state =
        if receiving == some old then .ok (old, owner, [old]) state else
          match owner.use with
          | .replacement _ => match exitLandingAnchor fuel old row.storage receiving state with
            | .ok (anchor, destination, chain) final => .ok (anchor, destination, old :: chain) final
            | .fault reason final => .fault reason final
          | _ => if receiving.isSome then .fault .ownership state else .ok (old, owner, [old]) state := by
      simp only [exitLandingAnchor, lookupDestination_result, present, use, ownerFound, shape,
        Bool.false_eq_true, ↓reduceIte, bind, pure]
      rcases progress with ⟨count, progress⟩ | progress | progress <;>
        simp only [progress, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      all_goals
        split
        · rfl
        · cases owner.use
          · split <;> rfl
          · split <;> rfl
          · cases evaluated : exitLandingAnchor fuel old row.storage receiving state with
            | fault reason final => simp only [evaluated]
            | ok payload final =>
              obtain ⟨anchor, destination, chain⟩ := payload
              simp only [evaluated]
    by_cases hit : (receiving == some old) = true
    · refine ⟨old, owner, [old], ?_, ownerFound, sameBacking.symm, oldSupported, ?_, ?_⟩
      · rw [dispatch, hit]; rfl
      · intro receiver selectedReceiver
        have same := (beq_iff_eq).mp hit
        exact Option.some.inj (same.symm.trans selectedReceiver)
      · intro absent
        rw [absent] at hit
        cases hit
    · have notHit : (receiving == some old) = false := Bool.eq_false_iff.mpr hit
      have tailBoundary : ∀ receiver, receiving = some receiver →
          OwnershipReplacementPath state.destinations receiver old := by
        intro receiver selectedReceiver
        obtain ⟨earlier, path⟩ := boundary receiver selectedReceiver
        exact replacementPath_tail state receiver selected old row present use path (Nat.ne_of_lt earlier)
      cases ownerUse : owner.use with
      | replacement parent =>
        have innerBoundary : ∀ receiver, receiving = some receiver → receiver < old ∧
            OwnershipReplacementPath state.destinations receiver old := by
          intro receiver selectedReceiver
          have path := tailBoundary receiver selectedReceiver
          have lower := path.le ordered
          have different : receiver ≠ old := by
            intro same
            subst receiver
            simp only [selectedReceiver, beq_self_eq_true, Bool.true_eq_false] at notHit
          exact ⟨Nat.lt_of_le_of_ne lower different, path⟩
        obtain ⟨anchor, destination, chain, recursive, found, backing, anchorSupported, selectedReceiver, terminal⟩ :=
          ih old parent owner ownerFound ownerUse oldSupported (by omega) innerBoundary
        rw [storageSame] at recursive
        refine ⟨anchor, destination, old :: chain, ?_, found, backing.trans sameBacking.symm, anchorSupported, selectedReceiver, terminal⟩
        simp only [dispatch, notHit, ownerUse, recursive, Bool.false_eq_true, ↓reduceIte]
      | receiver | child parent =>
        have terminal : ∀ parent, owner.use ≠ .replacement parent := by
          intro ancestor same
          simp only [ownerUse] at same
          cases same
        have absent : receiving = none := by
          cases selectedReceiver : receiving with
          | none => rfl
          | some receiver =>
            have same := replacementPath_terminal state receiver old owner ownerFound terminal
              (tailBoundary receiver selectedReceiver)
            subst receiver
            simp only [selectedReceiver, beq_self_eq_true, Bool.true_eq_false] at notHit
        refine ⟨old, owner, [old], ?_, ownerFound, sameBacking.symm, oldSupported, ?_, fun _ => terminal⟩
        · rw [dispatch, absent, ownerUse]
          rfl
        · intro receiver selectedReceiver
          rw [absent] at selectedReceiver
          cases selectedReceiver

#print axioms exitLandingAnchor_supported

end Goose.Proofs.ExitExecution

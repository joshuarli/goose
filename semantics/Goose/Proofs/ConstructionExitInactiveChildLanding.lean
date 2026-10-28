import Goose.Proofs.ConstructionExitLandingChildAnchor

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem inactive_child_landing_violates_unique (state : ConstructionState)
    (id old count parentId parentCount siblingId : Nat)
    (replacement anchor parent sibling : PendingDestination) (storage : ReceivingStorage)
    (indexed : DestinationCapabilitiesIndexed state) (ordered : DestinationOwnersOrdered state)
    (replacementFound : state.destinations[id]? = some replacement)
    (replacementUse : ∃ prior, replacement.use = .replacement prior)
    (stored : state.storage[replacement.storage]? = some storage)
    (anchorUse : anchor.use = .child parentId)
    (siblingFound : state.destinations[siblingId]? = some sibling)
    (siblingUse : sibling.use = .child parentId) (siblingActive : activeRow sibling = true)
    (siblingOutside : destinationDescendant state.destinations old siblingId = false)
    (startOrder : anchor.capability.start ≤ replacement.capability.start)
    (inside : replacement.capability.start ≤ storage.bytes.size)
    (parentFound : state.destinations[parentId]? = some parent) (parentDifferent : parentId ≠ id) :
    ∃ after, completedStep id old count replacement anchor
      (some (parentId, { parent with progress := .suspended parentCount id })) state = .ok () after ∧
      ¬ ActiveChildUnique after := by
  have parentEarlier : parentId < siblingId := by simpa only [siblingUse] using ordered siblingId sibling siblingFound
  have idDifferent : id ≠ siblingId := by
    intro equal
    rw [equal] at replacementFound
    have same := Option.some.inj (siblingFound.symm.trans replacementFound)
    subst replacement
    obtain ⟨prior, use⟩ := replacementUse
    rw [siblingUse] at use
    cases use
  let updated := { parent with progress := .suspended parentCount id }
  let final := completedLandingState state id old count replacement anchor storage (some (parentId, updated))
  have bound : ∀ actualId actual, some (parentId, updated) = some (actualId, actual) → actualId < state.destinations.size := by
    intro actualId actual equal
    have same : parentId = actualId := congrArg Prod.fst (Option.some.inj equal)
    rw [← same]
    exact (Array.getElem?_eq_some_iff.mp parentFound).1
  have execution := completedStep_success state id old count replacement anchor storage
    (some (parentId, updated)) indexed replacementFound stored startOrder inside bound
  have replacementAfter : final.destinations[id]? = some (landedReplacementRow replacement anchor count) := by
    apply completedLandingState_replacement state id old count replacement anchor storage (some (parentId, updated))
      (Array.getElem?_eq_some_iff.mp replacementFound).1
    intro actualId actual equal
    have same : parentId = actualId := congrArg Prod.fst (Option.some.inj equal)
    simpa only [← same] using parentDifferent
  have siblingAfter : final.destinations[siblingId]? = some sibling := by
    have unchanged := completedLandingState_outside_destination state id old count replacement anchor storage
      (some (parentId, updated)) siblingId idDifferent (by
        intro row member equal
        have descendant := ((protectedRows_exact_selection state old id row).mp member).2.2.1
        rw [equal, siblingOutside] at descendant
        cases descendant) (by
        intro actualId actual equal
        have same : parentId = actualId := congrArg Prod.fst (Option.some.inj equal)
        rw [← same]
        exact Nat.ne_of_lt parentEarlier)
    exact unchanged.trans siblingFound
  refine ⟨final, execution, ?_⟩
  intro valid
  have equal := valid parentId id siblingId (landedReplacementRow replacement anchor count) sibling
    replacementAfter (by simp [landedReplacementRow, anchorUse]) (by simp [landedReplacementRow, activeRow])
    siblingAfter siblingUse siblingActive
  exact idDifferent equal

theorem inactive_child_commit_violates_unique (state : ConstructionState)
    (id old count parentId parentCount siblingId : Nat)
    (replacement anchor parent sibling : PendingDestination) (storage : ReceivingStorage)
    (receiving : Option DestinationId) (chain : List DestinationId)
    (lifecycle : DestinationLifecycleInvariant state)
    (replacementFound : state.destinations[id]? = some replacement) (built : replacement.progress = .built count)
    (replacementUse : ∃ prior, replacement.use = .replacement prior)
    (stored : state.storage[replacement.storage]? = some storage)
    (selected : exitLandingAnchor (state.destinations.size + 1) id replacement.storage receiving state =
      .ok (old, anchor, chain) state)
    (anchorUse : anchor.use = .child parentId)
    (parentFound : state.destinations[parentId]? = some parent) (parentPhase : parent.progress = .suspended parentCount old)
    (siblingFound : state.destinations[siblingId]? = some sibling) (siblingUse : sibling.use = .child parentId)
    (siblingActive : activeRow sibling = true) (siblingOutside : destinationDescendant state.destinations old siblingId = false)
    (startOrder : anchor.capability.start ≤ replacement.capability.start)
    (inside : replacement.capability.start ≤ storage.bytes.size) :
    ∃ after, commitExitReplacement receiving id state = .ok () after ∧ ¬ ActiveChildUnique after := by
  obtain ⟨_, anchorEarlier, anchorPresent⟩ := exitLandingAnchor_success _ _ _ _ state state old anchor chain selected
  have parentEarlier : parentId < old := by simpa only [anchorUse] using lifecycle.2.2.2 old anchor anchorPresent
  have parentDifferent : parentId ≠ id := Nat.ne_of_lt (Nat.lt_trans parentEarlier anchorEarlier)
  let update := some (parentId, { parent with progress := .suspended parentCount id })
  have bound : ∀ actualId actual, update = some (actualId, actual) → actualId < state.destinations.size := by
    intro actualId actual same
    have ids : parentId = actualId := congrArg Prod.fst (Option.some.inj same)
    rw [← ids]
    exact (Array.getElem?_eq_some_iff.mp parentFound).1
  have step := completedStep_success state id old count replacement anchor storage update lifecycle.2.1 replacementFound stored startOrder inside bound
  have executed : commitExitReplacement receiving id state = .ok ()
      (committedExitState state id old count replacement anchor storage update chain) := by
    simp only [commitExitReplacement, lookupDestination_result, replacementFound, built, ConstructionM.get,
      selected, anchorUse, parentFound, parentPhase, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      bind, pure]
    simp only [completedStep, update] at step
    rw [step]
    rfl
  obtain ⟨landed, land, notUnique⟩ := inactive_child_landing_violates_unique state id old count parentId parentCount siblingId
    replacement anchor parent sibling storage lifecycle.2.1 lifecycle.2.2.2 replacementFound replacementUse stored anchorUse
    siblingFound siblingUse siblingActive siblingOutside startOrder inside parentFound parentDifferent
  have expected := completedStep_success state id old count replacement anchor storage update lifecycle.2.1 replacementFound stored startOrder inside bound
  have same := (ConstructionResult.ok.inj (land.symm.trans expected)).2
  rw [same] at notUnique
  refine ⟨_, executed, ?_⟩
  simpa only [committedExitState, ActiveChildUnique] using notUnique

theorem unique_sibling_forces_inactive_anchor (state : ConstructionState)
    (old parentId siblingId : Nat) (anchor sibling : PendingDestination)
    (unique : ActiveChildUnique state) (anchorFound : state.destinations[old]? = some anchor)
    (anchorUse : anchor.use = .child parentId) (siblingFound : state.destinations[siblingId]? = some sibling)
    (siblingUse : sibling.use = .child parentId) (siblingActive : activeRow sibling = true)
    (siblingOutside : destinationDescendant state.destinations old siblingId = false) : activeRow anchor = false := by
  have different : old ≠ siblingId := by
    intro equal
    rw [← equal] at siblingOutside
    have self := destinationDescendant_self state old (Array.getElem?_eq_some_iff.mp anchorFound).1
    rw [self] at siblingOutside
    cases siblingOutside
  cases active : activeRow anchor with
  | false => rfl
  | true => exact False.elim (different (unique parentId old siblingId anchor sibling anchorFound anchorUse active
      siblingFound siblingUse siblingActive))

#print axioms unique_sibling_forces_inactive_anchor
#print axioms inactive_child_commit_violates_unique
#print axioms inactive_child_landing_violates_unique

end Goose.Proofs.ConstructionAcceptedExecution

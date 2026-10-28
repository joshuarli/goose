import Goose.Proofs.ConstructionExitUniqueChildren
import Goose.Proofs.ConstructionExecutionOwnershipCleanup

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership

theorem abandonRows_active_source (before : ConstructionState) (rows : List PendingDestination)
    (bounded : ∀ row ∈ rows, row.capability.id < before.destinations.size)
    (unique : rows.Pairwise fun first second => first.capability.id ≠ second.capability.id)
    (id : Nat) (row : PendingDestination)
    (present : (abandonRowsState rows before).destinations[id]? = some row) (active : activeRow row = true) :
    before.destinations[id]? = some row := by
  classical
  by_cases member : ∃ selected ∈ rows, selected.capability.id = id
  · obtain ⟨selected, selectedMember, equal⟩ := member
    have abandoned := abandonRowsState_inside rows before bounded unique selected selectedMember
    rw [equal] at abandoned
    have same := Option.some.inj (abandoned.symm.trans present)
    subst row
    simp [activeRow] at active
  · have untouched := abandonRowsState_outside rows before id (by
      intro selected selectedMember equal
      exact member ⟨selected, selectedMember, equal⟩)
    simpa only [untouched] using present

theorem abandonRows_preserves_unique_children (before : ConstructionState) (rows : List PendingDestination)
    (bounded : ∀ row ∈ rows, row.capability.id < before.destinations.size)
    (distinct : rows.Pairwise fun first second => first.capability.id ≠ second.capability.id)
    (valid : ActiveChildUnique before) : ActiveChildUnique (abandonRowsState rows before) := by
  intro parent first second left right leftFound leftUse leftActive rightFound rightUse rightActive
  exact valid parent first second left right
    (abandonRows_active_source before rows bounded distinct first left leftFound leftActive) leftUse leftActive
    (abandonRows_active_source before rows bounded distinct second right rightFound rightActive) rightUse rightActive

theorem abandonPreservingExit_preserves_unique_children (before after : ConstructionState)
    (id replacement : Nat) (indexed : DestinationCapabilitiesIndexed before)
    (valid : ActiveChildUnique before)
    (executed : abandonPreservingExit id replacement before = .ok () after) : ActiveChildUnique after := by
  have checked : ∃ rows, protectedExitDiscarded before id replacement = .ok rows := by
    simp only [abandonPreservingExit, ConstructionM.get, bind] at executed
    cases result : protectedExitDiscarded before id replacement with
    | error fault => simp [result, ConstructionM.fail] at executed
    | ok rows => exact ⟨rows, rfl⟩
  have exactResult := abandonPreservingExit_exact before id replacement indexed checked
  have same := ConstructionResult.ok.inj (exactResult.symm.trans executed)
  rw [← same.2]
  exact abandonRows_preserves_unique_children before (protectedRows before id replacement)
    (protectedRows_indexed before id replacement indexed).1
    (protectedRows_indexed before id replacement indexed).2 valid

#print axioms abandonRows_active_source
#print axioms abandonRows_preserves_unique_children
#print axioms abandonPreservingExit_preserves_unique_children

end Goose.Proofs.ConstructionAcceptedExecution

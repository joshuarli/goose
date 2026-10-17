import Goose.Proofs.ConstructionExecutionProtocolOwners

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

abbrev destinationDescendant (destinations : Array PendingDestination)
    (ancestor id : DestinationId) : Bool :=
  (fun {left right : Bool} (_ : left = right) => left)
    (descendantOf_result destinations ancestor id)

private theorem list_forIn_invariant {α β : Type} (items : List α)
    (action : α → β → Id (ForInStep β)) (invariant : β → Prop)
    (preserved : ∀ item state, invariant state → invariant (action item state).value)
    (initial : β) (valid : invariant initial) :
    invariant (forIn items initial action : Id β) := by
  induction items generalizing initial with
  | nil => exact valid
  | cons item rest ih =>
      have one := preserved item initial valid
      rw [List.forIn_cons]
      cases step : action item initial with
      | done after => simpa only [step, ForInStep.value, bind, pure] using one
      | yield after => exact ih after (by simpa only [step, ForInStep.value, bind, pure] using one)

theorem destinationDescendant_le (state : ConstructionState)
    (ordered : DestinationOwnersOrdered state) (ancestor id : DestinationId)
    (descendant : destinationDescendant state.destinations ancestor id = true) : ancestor ≤ id := by
  dsimp only [destinationDescendant] at descendant
  rw [descendantOf_result] at descendant
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at descendant
  generalize run : (forIn (List.range' 0 ([:state.destinations.size] : Std.Legacy.Range).size) (none, id) _ : Id (Option Bool × Nat)) = output at descendant
  have bound : output.2 ≤ id ∧ (output.1 = some true → ancestor ≤ id) := by
    rw [← run]
    apply list_forIn_invariant
      (invariant := fun result : Option Bool × Nat =>
        result.2 ≤ id ∧ (result.1 = some true → ancestor ≤ id))
    · intro item current prior
      by_cases same : current.2 = ancestor
      · simpa [same, pure] using prior.1
      · cases row : state.destinations[current.2]? with
        | none => simpa [same, row, pure] using prior.1
        | some destination =>
            cases use : destination.use with
            | receiver => simpa [same, row, use, pure] using prior.1
            | child parent | replacement parent =>
                have parentBound : parent ≤ id := Nat.le_trans
                  (Nat.le_of_lt (by simpa [use] using ordered current.2 destination row)) prior.1
                simpa [same, row, use, pure] using parentBound
    · exact ⟨Nat.le_refl id, by simp⟩
  apply bound.2
  change output.1.getD false = true at descendant
  cases valueRow : output.1 with
  | none => simp [valueRow] at descendant
  | some value =>
      cases value with
      | false => simp [valueRow] at descendant
      | true => rfl

theorem destinationDescendant_false_of_lt (state : ConstructionState)
    (ordered : DestinationOwnersOrdered state) (ancestor id : DestinationId)
    (earlier : id < ancestor) : destinationDescendant state.destinations ancestor id = false := by
  cases found : destinationDescendant state.destinations ancestor id with
  | false => rfl
  | true => exact False.elim (Nat.not_le_of_lt earlier
      (destinationDescendant_le state ordered ancestor id found))

theorem destinationDescendant_congr_uses (before after : Array PendingDestination)
    (same : before.map (·.use) = after.map (·.use)) (ancestor id : DestinationId) :
    destinationDescendant before ancestor id = destinationDescendant after ancestor id := by
  have size : after.size = before.size := by
    have equal := congrArg Array.size same
    simpa using equal.symm
  have lookup (current : DestinationId) :
      (before[current]?).map (·.use) = (after[current]?).map (·.use) := by
    have equal := congrArg (fun uses => uses[current]?) same
    simpa only [Array.getElem?_map] using equal
  dsimp only [destinationDescendant]
  rw [descendantOf_result, descendantOf_result]
  simp only [size, Std.Legacy.Range.forIn_eq_forIn_range']
  apply congrArg (fun result : Option Bool × Nat => result.1.getD false)
  congr 1
  funext item current
  have row := lookup current.2
  by_cases found : current.2 = ancestor
  · simp [found]
  · cases beforeRow : before[current.2]? <;>
      cases afterRow : after[current.2]? <;> simp_all

theorem destinationDescendant_replace_use (destinations : Array PendingDestination)
    (index : DestinationId) (before after : PendingDestination)
    (present : destinations[index]? = some before) (use : after.use = before.use)
    (ancestor id : DestinationId) :
    destinationDescendant (destinations.set! index after) ancestor id =
      destinationDescendant destinations ancestor id := by
  apply destinationDescendant_congr_uses
  apply Array.ext_getElem?
  intro current
  simp only [Array.getElem?_map]
  by_cases same : index = current
  · subst current
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside, present, use]
  · simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same]

end Goose.Proofs.ConstructionExecutionProtocol

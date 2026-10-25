import Goose.Construct.DestinationTrace
import Init.Data.Range.Lemmas

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

private theorem list_forIn_congr_of_invariant {α β : Type} (items : List α)
    (left right : α → β → Id (ForInStep β)) (invariant : β → Prop)
    (equal : ∀ item state, invariant state → left item state = right item state)
    (preserved : ∀ item before after, invariant before →
      left item before = .yield after → invariant after)
    (initial : β) (valid : invariant initial) :
    (forIn items initial left : Id β) = forIn items initial right := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.forIn_cons, equal item initial valid]
      cases step : right item initial with
      | done after => rfl
      | yield after =>
          exact ih after (preserved item initial after valid ((equal item initial valid).trans step))

theorem destinationCanWrite_congr_of_owner_prefix (before after : ConstructionState)
    (id : DestinationId) (ordered : DestinationOwnersOrdered before)
    (size : after.destinations.size = before.destinations.size)
    (uses : ∀ current, current ≤ id →
      (before.destinations[current]?).map (·.use) = (after.destinations[current]?).map (·.use))
    (progress : ∀ current, current < id →
      (before.destinations[current]?).map (·.progress) =
        (after.destinations[current]?).map (·.progress)) :
    destinationCanWrite before id = destinationCanWrite after id := by
  unfold destinationCanWrite
  simp only [size, Std.Legacy.Range.forIn_eq_forIn_range']
  apply congrArg (fun result : Option Bool × Nat => result.1.getD false)
  apply list_forIn_congr_of_invariant
    (invariant := fun result : Option Bool × Nat => result.2 ≤ id)
  · intro item state bounded
    have same := uses state.2 bounded
    cases beforeRow : before.destinations[state.2]? with
    | none =>
        cases afterRow : after.destinations[state.2]? <;> simp_all
    | some owner =>
        cases afterRow : after.destinations[state.2]? with
        | none => simp_all
        | some other =>
            have sameUse : owner.use = other.use := by simpa [beforeRow, afterRow] using same
            cases ownerUse : owner.use with
            | receiver => simp [← sameUse, ownerUse]
            | child parent | replacement parent =>
                have parentBound : parent < id := Nat.lt_of_lt_of_le
                  (by simpa [ownerUse] using ordered state.2 owner beforeRow) bounded
                simp only [← sameUse, ownerUse]
                have sameProgress := progress parent parentBound
                cases parentBefore : before.destinations[parent]? <;>
                  cases parentAfter : after.destinations[parent]? <;>
                  simp_all
  · intro item state next bounded yielded
    cases row : before.destinations[state.2]? with
    | none => simp [row] at yielded
    | some owner =>
        cases ownerUse : owner.use with
        | receiver => simp [row, ownerUse] at yielded
        | child parent | replacement parent =>
            have parentBound : parent ≤ id := Nat.le_trans
              (Nat.le_of_lt (by simpa [ownerUse] using ordered state.2 owner row)) bounded
            simp only [row, ownerUse] at yielded
            repeat' first | split at yielded | simp_all [pure]
            all_goals cases yielded; exact parentBound
  · exact Nat.le_refl id

theorem destinationCanWrite_replace_progress (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (progress : DestinationProgress)
    (present : state.destinations[id]? = some destination)
    (ordered : DestinationOwnersOrdered state) :
    destinationCanWrite { state with destinations := state.destinations.set! id ({ destination with progress := progress }) } id =
      destinationCanWrite state id := by
  symm
  apply destinationCanWrite_congr_of_owner_prefix state _ id ordered
  · simp
  · intro current bounded
    by_cases same : id = current
    · subst current
      have inside := (Array.getElem?_eq_some_iff.mp present).1
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside, present]
    · simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same]
  · intro current bounded
    have different : id ≠ current := (Nat.ne_of_lt bounded).symm
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different]

theorem destinationCanWrite_replace_later (state : ConstructionState) (id changed : DestinationId)
    (destination : PendingDestination) (later : id < changed)
    (ordered : DestinationOwnersOrdered state) :
    destinationCanWrite { state with destinations := state.destinations.set! changed destination } id =
      destinationCanWrite state id := by
  symm
  apply destinationCanWrite_congr_of_owner_prefix state _ id ordered
  · simp
  · intro current bounded
    have different : changed ≠ current := (Nat.ne_of_lt (Nat.lt_of_le_of_lt bounded later)).symm
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different]
  · intro current bounded
    have different : changed ≠ current := (Nat.ne_of_lt (Nat.lt_trans bounded later)).symm
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different]

theorem destinationCanWrite_congr_destinations (before after : ConstructionState) (id : DestinationId)
    (destinations : before.destinations = after.destinations) :
    destinationCanWrite before id = destinationCanWrite after id := by
  simp only [destinationCanWrite, destinations]

end Goose.Proofs.ConstructionExecutionProtocol

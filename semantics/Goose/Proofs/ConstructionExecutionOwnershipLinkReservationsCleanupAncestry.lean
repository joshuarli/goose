import Goose.Proofs.ConstructionExecutionOwnershipReplacementSupport
import Goose.Proofs.ConstructionExecutionProtocolOwnersAncestry

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

inductive OwnershipReplacementPath (rows : Array PendingDestination) : DestinationId → DestinationId → Prop
  | refl (id : DestinationId) : OwnershipReplacementPath rows id id
  | step (id parent ancestor : DestinationId) (row : PendingDestination)
      (present : rows[id]? = some row) (use : row.use = .replacement parent)
      (path : OwnershipReplacementPath rows ancestor parent) : OwnershipReplacementPath rows ancestor id

theorem OwnershipReplacementPath.trans {rows : Array PendingDestination} {ancestor middle id : DestinationId}
    (first : OwnershipReplacementPath rows ancestor middle) (second : OwnershipReplacementPath rows middle id) :
    OwnershipReplacementPath rows ancestor id := by
  induction second with
  | refl => exact first
  | step id parent middle row present use path ih => exact .step id parent ancestor row present use (ih first)

theorem replacementSupported_active_path (state : ConstructionState) (id : DestinationId)
    (supported : ReplacementSupported state id) :
    ∃ leaf row, state.destinations[leaf]? = some row ∧ activeProgress row.progress = true ∧
      OwnershipReplacementPath state.destinations id leaf := by
  induction supported with
  | active id row present live => exact ⟨id, row, present, live, .refl id⟩
  | parent id parent row present use supported ih =>
      obtain ⟨leaf, activeRow, activePresent, live, path⟩ := ih
      exact ⟨leaf, activeRow, activePresent, live,
        OwnershipReplacementPath.trans (.step id parent parent row present use (.refl parent)) path⟩

def ancestryWalk (rows : Array PendingDestination) (ancestor : DestinationId) : Nat → DestinationId → Bool
  | 0, _ => false
  | fuel + 1, id =>
      if id == ancestor then true else
        match rows[id]? with
        | none => false
        | some row => match row.use with
          | .receiver => false
          | .child parent | .replacement parent => ancestryWalk rows ancestor fuel parent

private def ancestryStep (rows : Array PendingDestination) (ancestor : DestinationId)
    (current : Option Bool × Nat) : Id (ForInStep (Option Bool × Nat)) :=
  if current.2 == ancestor then pure (.done (some true, current.2)) else
    match rows[current.2]? with
    | some row => match row.use with
      | .receiver => pure (.done (some false, current.2))
      | .replacement parent => pure (.yield (none, parent))
      | .child parent => pure (.yield (none, parent))
    | _ => pure (.done (some false, current.2))

private theorem ancestryLoop_walk (rows : Array PendingDestination) (ancestor start fuel id : Nat) :
    (forIn (List.range' start fuel) (none, id)
      (fun _ current => ancestryStep rows ancestor current) : Id (Option Bool × Nat)).1.getD false =
        ancestryWalk rows ancestor fuel id := by
  induction fuel generalizing start id with
  | zero => rfl
  | succ fuel ih =>
      simp only [List.range'_succ, List.forIn_cons, ancestryStep, ancestryWalk]
      split
      · rfl
      · cases present : rows[id]? with
        | none => rfl
        | some row =>
            cases use : row.use with
            | receiver => simp only [use, bind, pure]; rfl
            | child parent | replacement parent =>
                simpa only [ancestryStep, use, bind, pure] using ih (start + 1) parent

theorem destinationDescendant_walk (rows : Array PendingDestination) (ancestor id : DestinationId) :
    destinationDescendant rows ancestor id = ancestryWalk rows ancestor rows.size id := by
  dsimp only [destinationDescendant]
  rw [descendantOf_result]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Id.run, bind, pure]
  have size : ([:rows.size] : Std.Legacy.Range).size = rows.size := by simp [Std.Legacy.Range.size]
  simp only [size]
  change (forIn (List.range' 0 rows.size) (none, id)
    (fun _ current => ancestryStep rows ancestor current) : Id (Option Bool × Nat)).1.getD false = _
  exact ancestryLoop_walk rows ancestor 0 rows.size id


theorem OwnershipReplacementPath.le {state : ConstructionState} (ordered : DestinationOwnersOrdered state)
    {ancestor id : DestinationId} (path : OwnershipReplacementPath state.destinations ancestor id) : ancestor ≤ id := by
  induction path with
  | refl => exact Nat.le_refl _
  | step id parent ancestor row present use path ih =>
      exact Nat.le_trans ih (Nat.le_of_lt (by simpa only [use] using ordered id row present))

private theorem replacementPath_walk {state : ConstructionState} (ordered : DestinationOwnersOrdered state)
    {ancestor id : DestinationId} (path : OwnershipReplacementPath state.destinations ancestor id) :
    ∀ fuel, id < fuel → ancestryWalk state.destinations ancestor fuel id = true := by
  induction path with
  | refl id =>
      intro fuel bound
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ bound)
      | succ fuel => simp [ancestryWalk]
  | step id parent ancestor row present use path ih =>
      intro fuel bound
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ bound)
      | succ fuel =>
          by_cases same : id = ancestor
          · simp [ancestryWalk, same]
          · have earlier : parent < id := by simpa only [use] using ordered id row present
            have enough := Nat.lt_of_lt_of_le earlier (Nat.le_of_lt_succ bound)
            simpa only [ancestryWalk, beq_iff_eq, same, ↓reduceIte, present, use] using ih fuel enough

theorem OwnershipReplacementPath.descendant {state : ConstructionState}
    (ordered : DestinationOwnersOrdered state) {ancestor id : DestinationId}
    (path : OwnershipReplacementPath state.destinations ancestor id) (inside : id < state.destinations.size) :
    destinationDescendant state.destinations ancestor id = true := by
  rw [destinationDescendant_walk]
  exact replacementPath_walk ordered path _ inside



def OwnershipUsesBackExcept (before after : ConstructionState) (ignored : DestinationId) : Prop :=
  ∀ id row, after.destinations[id]? = some row → id ≠ ignored →
    ∃ original, before.destinations[id]? = some original ∧ original.use = row.use

theorem OwnershipReplacementPath.ne_rewired {state : ConstructionState}
    (ordered : DestinationOwnersOrdered state) {ancestor id ignored : DestinationId}
    (rewired : PendingDestination) (present : state.destinations[ignored]? = some rewired)
    (outside : ∀ parent, rewired.use = .replacement parent → parent < ancestor)
    (different : ancestor ≠ ignored) (path : OwnershipReplacementPath state.destinations ancestor id) :
    id ≠ ignored := by
  cases path with
  | refl => exact different
  | step id parent ancestor row found use path =>
      intro same
      subst id
      have equal := Option.some.inj (found.symm.trans present)
      subst row
      exact Nat.not_le_of_lt (outside parent use) (path.le ordered)

theorem OwnershipReplacementPath.before_rewire {before after : ConstructionState}
    (ordered : DestinationOwnersOrdered after) {ancestor id ignored : DestinationId}
    (rewired : PendingDestination) (present : after.destinations[ignored]? = some rewired)
    (outside : ∀ parent, rewired.use = .replacement parent → parent < ancestor)
    (uses : OwnershipUsesBackExcept before after ignored)
    (path : OwnershipReplacementPath after.destinations ancestor id) :
    OwnershipReplacementPath before.destinations ancestor id := by
  induction path with
  | refl id => exact .refl id
  | step id parent ancestor row found use path ih =>
      have different : id ≠ ignored := by
        intro same
        subst id
        have equal := Option.some.inj (found.symm.trans present)
        subst row
        exact Nat.not_le_of_lt (outside parent use) (path.le ordered)
      obtain ⟨original, originalPresent, originalUse⟩ := uses id row found different
      exact .step id parent ancestor original originalPresent (originalUse.trans use) (ih outside)



theorem OwnershipReplacementPath.before_sources {before after : ConstructionState}
    (sources : ∀ (id : DestinationId) (row : PendingDestination), after.destinations[id]? = some row →
      ∃ original : PendingDestination, before.destinations[id]? = some original ∧ original.use = row.use)
    {ancestor id : DestinationId} (path : OwnershipReplacementPath after.destinations ancestor id) :
    OwnershipReplacementPath before.destinations ancestor id := by
  induction path with
  | refl id => exact .refl id
  | step id parent ancestor row found use path ih =>
      obtain ⟨original, originalPresent, originalUse⟩ := sources id row found
      exact .step id parent ancestor original originalPresent (originalUse.trans use) ih


#print axioms destinationDescendant_walk

end Goose.Proofs.ConstructionExecutionOwnership

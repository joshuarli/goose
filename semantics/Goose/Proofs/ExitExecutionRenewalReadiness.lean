import Goose.Proofs.ExitExecutionReceiverReadiness

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionOwnership

local syntax "renewal_split_at " ident : tactic
elab_rules : tactic
  | `(tactic| renewal_split_at $name:ident) => do
      let hypothesis ← Lean.Elab.Tactic.getFVarId name
      Lean.Elab.Tactic.liftMetaTactic fun goal => do
        let some (yes, no) ← Lean.Meta.SplitIf.splitIfAt? goal (← Lean.Meta.inferType (.fvar hypothesis)) none
          | Lean.throwError "no renewal condition"
        return [yes.mvarId, no.mvarId]

private abbrev renewalPrefix : ReceivingLayout → ConstructionRequest → Bool := renewal_prefix_test
private abbrev renewalPrefixBytes : ByteArray := renewal_prefix_bytes

private def renewedDestination (state : ConstructionState) (snapshot : PendingDestination) : PendingDestination :=
  { snapshot with
    capability := { snapshot.capability with id := state.destinations.size }
    progress := .open 0
    writeEnd := snapshot.capability.start + (if renewalPrefix snapshot.layout snapshot.capability.request then 4 else 0) }

private def renewalTail (snapshot : PendingDestination) (storage : ReceivingStorage) (next : Nat)
    (update : Option (DestinationId × PendingDestination)) : ConstructionM Nat := do
  if let some (parent, owner) := update then destinationReplace parent owner
  storageReplace snapshot.storage storage
  if renewalPrefix snapshot.layout snapshot.capability.request then
    storageReplace snapshot.storage { storage with bytes := storage.bytes ++ renewalPrefixBytes }
  eventEmit (.begin next)
  match snapshot.backing with
  | .staged _ _ => eventEmit (.stage next)
  | .direct _ => pure ()
  pure next

private def renewalParented (state : ConstructionState) (update : Option (DestinationId × PendingDestination)) : Array PendingDestination :=
  match update with
  | none => state.destinations
  | some (parent, owner) => state.destinations.set! parent owner

private theorem renewalTail_destinations (snapshot : PendingDestination) (storage : ReceivingStorage) (next : Nat)
    (update : Option (DestinationId × PendingDestination)) (state after : ConstructionState) (id : Nat)
    (executed : renewalTail snapshot storage next update state = .ok id after) :
    id = next ∧ after.destinations = renewalParented state update ∧
      after.destinationSuccessors = state.destinationSuccessors := by
  cases update <;> cases backing : snapshot.backing <;>
    cases needs : renewalPrefix snapshot.layout snapshot.capability.request <;>
    simp only [renewalTail, renewalParented, destinationReplace, storageReplace, eventEmit,
      replaceDestination_result, replaceStorage_result, emit_result, 
      backing, needs, Bool.false_eq_true, ↓reduceIte, bind, pure] at executed ⊢
  all_goals repeat' first
    | contradiction
    | simp_all only [ConstructionResult.ok.injEq, 
        Array.size_set!, ↓reduceIte]
    | renewal_split_at executed
    | rcases executed with ⟨rfl, rfl⟩
  all_goals exact ⟨True.intro, True.intro, True.intro⟩

private def renewalAllocation (state : ConstructionState) (old : Nat) (snapshot : PendingDestination)
    (storage : ReceivingStorage) : ConstructionM Nat := do
  let update ← match snapshot.use with
    | .receiver => pure none
    | .child parent => do
      let owner ← destinationLookup parent
      match owner.progress with
      | .suspended count expected =>
        if expected != old then ConstructionM.fail .ownership
        pure (some (parent, { owner with progress := .suspended count state.destinations.size }))
      | _ => ConstructionM.fail .protocol
    | .replacement parent => do
      let owner ← destinationLookup parent
      match owner.progress with
      | .exiting count expected =>
        if expected != old then ConstructionM.fail .ownership
        pure (some (parent, { owner with progress := .exiting count state.destinations.size }))
      | _ => ConstructionM.fail .protocol
  ConstructionM.set { state with
    destinations := state.destinations.push (renewedDestination state snapshot)
    destinationSuccessors := (old, state.destinations.size) :: state.destinationSuccessors }
  renewalTail snapshot storage state.destinations.size update

private theorem renewalAllocation_ready (state after : ConstructionState) (old id : Nat)
    (snapshot : PendingDestination) (storage : ReceivingStorage)
    (executed : renewalAllocation state old snapshot storage state = .ok id after) :
    id = state.destinations.size ∧ after.destinations.size = state.destinations.size + 1 ∧
      after.destinationSuccessors = (old, state.destinations.size) :: state.destinationSuccessors ∧
      ∃ row, after.destinations[id]? = some row ∧ LandingParentReady after id row ∧ row.progress = .open 0 := by
  let pushed : ConstructionState := { state with
    destinations := state.destinations.push (renewedDestination state snapshot)
    destinationSuccessors := (old, state.destinations.size) :: state.destinationSuccessors }
  cases use : snapshot.use with
  | receiver =>
    simp only [renewalAllocation, use, bind, pure, ConstructionM.set] at executed
    obtain ⟨rfl, table, successors⟩ := renewalTail_destinations snapshot storage state.destinations.size none pushed after id executed
    refine ⟨rfl, ?_, successors, renewedDestination state snapshot, ?_, .receiver use, rfl⟩
    · simp only [table, renewalParented, pushed, Array.size_push]
    · simp only [table, renewalParented, pushed, Array.getElem?_push_size]
  | child parent | replacement parent =>
    all_goals
      simp only [renewalAllocation, use, destinationLookup, lookupDestination_result, bind] at executed
      cases found : state.destinations[parent]? with
      | none => simp only [found] at executed; cases executed
      | some owner =>
        have parentInside := (Array.getElem?_eq_some_iff.mp found).1
        have parentDifferent : parent ≠ state.destinations.size := Nat.ne_of_lt parentInside
        simp only [found] at executed
        cases phase : owner.progress
        all_goals simp only [phase, ConstructionM.fail, pure] at executed
        all_goals try contradiction
        all_goals
          rename_i count expected
          renewal_split_at executed <;>
            simp_all only [ConstructionM.set, ↓reduceIte, reduceCtorEq]
          obtain ⟨rfl, table, successors⟩ := renewalTail_destinations snapshot storage state.destinations.size _ pushed after id executed
          refine ⟨rfl, ?_, successors, renewedDestination state snapshot, ?_, ?_, rfl⟩
          · simp only [table, renewalParented, pushed, Array.size_set!, Array.size_push]
          · simp only [table, renewalParented, pushed, Array.set!, Array.getElem?_setIfInBounds_ne parentDifferent, Array.getElem?_push_size]
          · first
              | refine LandingParentReady.child parent count { owner with progress := .suspended count state.destinations.size } (by exact use) ?_ rfl
              | refine LandingParentReady.replacement parent count { owner with progress := .exiting count state.destinations.size } (by exact use) ?_ rfl
            rw [table]
            apply Array.getElem?_setIfInBounds_self_of_lt
            simpa only [pushed, Array.size_push] using Nat.lt_succ_of_lt parentInside

private def renewalStorageThen (snapshot : PendingDestination) (storage : ReceivingStorage)
    (next : ReceivingStorage → ConstructionM Nat) : ConstructionM Nat := do
  let storage ← match snapshot.adaptation with
    | some receiving =>
      if renewalPrefix receiving.layout receiving.request && !renewalPrefix snapshot.layout snapshot.capability.request then
        if snapshot.capability.start != receiving.start + 4 || storage.bytes.size != receiving.start then ConstructionM.fail .ownership
        pure { storage with bytes := storage.bytes ++ renewalPrefixBytes }
      else pure storage
    | none => pure storage
  if storage.bytes.size < snapshot.capability.start then ConstructionM.fail .ownership
  next storage

private theorem renewalStorageThen_success (snapshot : PendingDestination) (storage : ReceivingStorage)
    (next : ReceivingStorage → ConstructionM Nat) (state after : ConstructionState) (id : Nat)
    (executed : renewalStorageThen snapshot storage next state = .ok id after) :
    ∃ receiving, next receiving state = .ok id after := by
  cases adaptation : snapshot.adaptation <;> simp only [renewalStorageThen, adaptation, bind, pure] at executed
  all_goals repeat' first
    | exact ⟨storage, executed⟩
    | exact ⟨{ storage with bytes := storage.bytes ++ renewalPrefixBytes }, executed⟩
    | contradiction
    | simp_all only [ConstructionM.fail, ↓reduceIte, reduceCtorEq]
    | renewal_split_at executed

private theorem renewReceivingDestination_ready_row (state after : ConstructionState) (incoming current id : Nat)
    (destination : PendingDestination)
    (resolved : destinationCurrent state incoming = .ok current)
    (present : state.destinations[current]? = some destination)
    (liveReady : destination.progress ≠ .abandoned → destination.progress ≠ .cancelled → LandingParentReady state current destination)
    (executed : renewReceivingDestination incoming state = .ok id after) :
    (after = state ∧ id = current ∧ LandingParentReady state current destination) ∨
      (id = state.destinations.size ∧ after.destinations.size = state.destinations.size + 1 ∧
        after.destinationSuccessors = (current, state.destinations.size) :: state.destinationSuccessors ∧
        ∃ row, after.destinations[id]? = some row ∧ LandingParentReady after id row ∧ row.progress = .open 0) := by
  simp only [renewReceivingDestination, ConstructionM.get, resolved, lookupDestination_result, present, bind, pure] at executed
  cases phase : destination.progress
  all_goals simp only [phase] at executed
  all_goals try
    cases executed
    exact Or.inl ⟨rfl, rfl, liveReady (by simp [phase]) (by simp [phase])⟩
  all_goals
    cases saved : state.destinationResumptions.lookup current with
    | none => simp only [saved, ConstructionM.fail] at executed; cases executed
    | some snapshot =>
      simp only [saved, lookupStorage_result] at executed
      cases stored : state.storage[snapshot.storage]? with
      | none => simp only [stored] at executed; cases executed
      | some storage =>
        simp only [stored] at executed
        have prepared : renewalStorageThen snapshot storage (renewalAllocation state current snapshot) state = .ok id after := by
          simp only [renewalStorageThen, renewalAllocation, renewalTail, renewedDestination, renewalPrefix, renewalPrefixBytes,
            destinationLookup, destinationReplace, storageReplace, eventEmit, lookupDestination_result, ConstructionM.fail,
            ConstructionM.set, bind, pure] at executed ⊢
          try unfold renewalAllocation.match_1 at executed ⊢
          try unfold renewalAllocation.match_2 at executed ⊢
          try unfold Goose.Construct.destinationCanWrite.match_1 at executed ⊢
          try unfold Goose.Construct.destinationCanWrite.match_2 at executed ⊢
          try unfold renewalPrefix at executed ⊢
          exact executed
        obtain ⟨receiving, success⟩ := renewalStorageThen_success snapshot storage (renewalAllocation state current snapshot) state after id prepared
        exact Or.inr (renewalAllocation_ready state after current id snapshot receiving success)

theorem renewReceivingDestination_receiving_ready (state after : ConstructionState)
    (incoming current id : Nat) (destination : PendingDestination)
    (valid : DestinationSuccessorsValid state)
    (resolved : destinationCurrent state incoming = .ok current)
    (present : state.destinations[current]? = some destination)
    (liveReady : destination.progress ≠ .abandoned → destination.progress ≠ .cancelled → LandingParentReady state current destination)
    (executed : renewReceivingDestination incoming state = .ok id after)
    (execution : ExecutionState) (construction : execution.construction = after) :
    Nonempty (ReceivingCarrierLandingReady execution incoming id) := by
  rcases renewReceivingDestination_ready_row state after incoming current id destination resolved present liveReady executed with
    ⟨rfl, rfl, parent⟩ | ⟨newId, size, successors, row, found, parent, phase⟩
  · exact ⟨⟨_, destination, destination, by simpa only [construction] using resolved,
      by simpa only [construction] using present, by simpa only [construction] using present,
      by rw [construction]; exact .refl _, by simpa only [construction] using parent, Nat.le_refl _⟩⟩
  · let pushed : ConstructionState := { state with destinations := state.destinations.push row }
    have pushedValid : DestinationSuccessorsValid pushed :=
      destinationSuccessorsValid_extension state pushed valid rfl (by simp [pushed])
    have currentInside := (Array.getElem?_eq_some_iff.mp present).1
    have incomingInside := destinationCurrent_source_bound state incoming current resolved
    have targetTerminal : state.destinationSuccessors.lookup id = none := by
      cases edge : state.destinationSuccessors.lookup id with
      | none => rfl
      | some next =>
        obtain ⟨lower, upper⟩ := valid id next edge
        rw [newId] at lower
        exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt lower) upper)
    have currentResolved := destinationCurrent_extension state pushed rfl (by simp [pushed]) incoming current resolved
    have postResolved : destinationCurrent after incoming = .ok id :=
      landingSuccessors_resolve pushed after [current] incoming current id pushedValid
        (by simpa only [pushed, Array.size_push] using size)
        (by simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, pushed, newId] using successors)
        (by simpa only [pushed, Array.size_push] using Nat.lt_succ_of_lt incomingInside)
        (by simp only [pushed, Array.size_push, newId]; omega)
        (by intro other member; simp only [List.mem_singleton] at member; simpa only [member, newId] using currentInside)
        currentResolved (by simp) targetTerminal
    exact ⟨⟨id, row, row, by simpa only [construction] using postResolved,
      by simpa only [construction] using found, by simpa only [construction] using found,
      by rw [construction]; exact .refl _, by simpa only [construction] using parent, Nat.le_refl _⟩⟩

#print axioms renewReceivingDestination_receiving_ready

end Goose.Proofs.ExitExecution

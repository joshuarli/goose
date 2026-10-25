import Goose.Proofs.ExitExecutionLandingSuccessors

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

private theorem abandonRowsState_channel_frame (rows : List PendingDestination) (state : ConstructionState) :
    (abandonRowsState rows state).destinationSuccessors = state.destinationSuccessors ∧
      (abandonRowsState rows state).exitReservations = state.exitReservations := by
  induction rows generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons row rest ih => exact ih _

private theorem completedLandingState_channel_frame (state : ConstructionState) (id old count : Nat)
    (replacement anchor : PendingDestination) (storage : ReceivingStorage)
    (parentUpdate : Option (DestinationId × PendingDestination)) :
    (completedLandingState state id old count replacement anchor storage parentUpdate).destinations.size = state.destinations.size ∧
    (completedLandingState state id old count replacement anchor storage parentUpdate).destinationSuccessors = state.destinationSuccessors ∧
    (completedLandingState state id old count replacement anchor storage parentUpdate).exitReservations = state.exitReservations := by
  have size := (abandonRowsState_frame (protectedRows state old id) state).2.2.1
  have frame := abandonRowsState_channel_frame (protectedRows state old id) state
  simp only [completedLandingState]
  split <;> cases parentUpdate <;> simp only [Array.size_set!, size, frame]
  all_goals exact ⟨True.intro, True.intro, True.intro⟩

private theorem storedValueBacking_tables (layout : LayoutEnv) (before after : ExecutionState) (stored : StoredValue)
    (backed : StoredValueBacking layout before stored)
    (storage : after.construction.storage = before.construction.storage)
    (destinations : after.construction.destinations = before.construction.destinations) :
    StoredValueBacking layout after stored := by
  cases backed with
  | detached receiving element present detached type interval =>
    exact .detached receiving element (by simpa only [storage] using present) detached type interval
  | named id receiving destination count present named binding backing type start progress element elementType interval =>
    exact .named id receiving destination count (by simpa only [storage] using present) named
      (by simpa only [destinations] using binding) backing type start progress element elementType interval

private theorem storedDestination_built (state : ExecutionState) (id count : Nat) (destination : PendingDestination)
    (present : state.construction.destinations[id]? = some destination)
    (built : destination.progress = .built count) :
    storedDestination id state = .ok
      ⟨destination.storage, destination.capability.start, destination.capability.logicalType, count, some id, none, [], count⟩ state := by
  simp only [storedDestination, getDestination, EvalM.get, present, bind, pure, built, progressCount]

private theorem replacementPath_use (state : ConstructionState) (receiving source : Nat) (row : PendingDestination)
    (present : state.destinations[source]? = some row)
    (path : OwnershipReplacementPath state.destinations receiving source) (different : receiving ≠ source) :
    ∃ parent, row.use = .replacement parent := by
  cases path with
  | refl => exact False.elim (different rfl)
  | step selected parent receiver actual found use tail =>
    have same := Option.some.inj (found.symm.trans present)
    subst actual
    exact ⟨parent, use⟩

inductive CompletedCarrierLandingFrame (before : ExecutionState) (incoming source : Nat) : ExecutionState → Prop
  | current : CompletedCarrierLandingFrame before incoming source before
  | commit (receiving count : Nat) (replacement anchor : PendingDestination) (storage : ReceivingStorage)
      (parentUpdate : Option (DestinationId × PendingDestination)) (chain : List DestinationId)
      (resolved : destinationCurrent before.construction incoming = .ok receiving)
      (present : before.construction.destinations[source]? = some replacement)
      (built : replacement.progress = .built count)
      (receivingPresent : before.construction.destinations[receiving]? = some anchor)
      (stored : before.construction.storage[replacement.storage]? = some storage)
      (sameStorage : anchor.storage = replacement.storage)
      (ordered : anchor.capability.start ≤ replacement.capability.start)
      (parentBound : ∀ parentId parent, parentUpdate = some (parentId, parent) → parentId < before.construction.destinations.size)
      (parentDifferent : ∀ parentId parent, parentUpdate = some (parentId, parent) → parentId ≠ source)
      (parentFootprint : ∀ parentId parent, parentUpdate = some (parentId, parent) →
        anchor.use = .child parentId ∨ anchor.use = .replacement parentId) :
      CompletedCarrierLandingFrame before incoming source
        { before with construction := committedExitState before.construction source receiving count replacement anchor storage parentUpdate chain }

theorem landCarriersInto_construct_completed (layout : LayoutEnv) (origin : OriginId)
    (state : ExecutionState) (ambient : OwnershipAmbient) (incoming source : Nat)
    (context : OwnershipExecutionContext state ambient)
    (backed : CarrierResultBacking layout state (.completed source))
    (ready : ReceivingCarrierLandingReady state incoming source) :
    ∃ after, landCarriersInto origin [.construct incoming] [.completed source] state = .ok () after ∧
      CarrierResultBacking layout after (.completed source) ∧
      Nonempty (ReceivingCarrierLandingReady after incoming source) ∧
      after.construction.exitReservations = state.construction.exitReservations ∧
      CompletedCarrierLandingFrame state incoming source after := by
  by_cases current : ready.receiving = source
  · exact ⟨state, landCarriersInto_current origin state incoming source ready current, backed, ⟨ready⟩, rfl, .current⟩
  cases backed with
  | completed id count replacement stored present built sampled backing =>
    have same := Option.some.inj (ready.sourcePresent.symm.trans present)
    have earlier : ready.receiving < source :=
      Nat.lt_of_le_of_ne (ready.path.le context.source.structural.1.1.1.2.2.2) current
    obtain ⟨old, use⟩ := replacementPath_use state.construction ready.receiving source replacement present ready.path current
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    have supported : ReplacementSupported state.construction source :=
      .active source replacement present (by simp only [built, activeProgress])
    obtain ⟨anchorId, anchor, chain, selected, anchorPresent, sameBacking, anchorSupported, selectedReceiving, _, member⟩ :=
      exitLandingAnchor_supported (state.construction.destinations.size + 1) state.construction
        context.source.structural.1.1.1.2.2.2 context.source.structural.1.2.2.1
        source old replacement (some ready.receiving) present use supported (by omega)
        (by intro receiver equal; cases equal; exact ⟨earlier, ready.path⟩)
    have anchorEq := selectedReceiving ready.receiving rfl
    subst anchorId
    have rowEq := Option.some.inj (anchorPresent.symm.trans ready.receivingPresent)
    subst anchor
    have canonical := storedDestination_built state source count replacement present built
    have storedEq : stored = ⟨replacement.storage, replacement.capability.start, replacement.capability.logicalType,
        count, some source, none, [], count⟩ := by
      have result := sampled.symm.trans canonical
      cases result
      rfl
    have named : stored.destination = some source := by rw [storedEq]
    obtain ⟨storage, run, storagePresent, sampledRun, interval⟩ := backing.sampled layout state stored
    have storedLookup : state.construction.storage[replacement.storage]? = some storage := by
      simpa only [storedEq] using storagePresent
    have startBound := storedValueBacking_named_start_bound layout state source count replacement storage stored
      backing named present storedLookup built
    have ordered : ready.receivingDestination.capability.start ≤ replacement.capability.start := by
      simpa only [same] using ready.ordered
    obtain ⟨parentUpdate, committed, parentBound, parentDifferent, parentFootprint, parentReady⟩ :=
      commitExitReplacement_of_anchor state.construction source count replacement storage (some ready.receiving) ready.receiving ready.receivingDestination chain
        context.source.structural.1.1.1 present built storedLookup selected ready.parent ordered startBound
    let result := committedExitState state.construction source ready.receiving count replacement
      ready.receivingDestination storage parentUpdate chain
    let after := { state with construction := result }
    let adopted := landedReplacementRow replacement ready.receivingDestination count
    have adoptedPresent : result.destinations[source]? = some adopted :=
      completedLandingState_replacement state.construction source ready.receiving count replacement
        ready.receivingDestination storage parentUpdate inside parentDifferent
    have adoptedBuilt : adopted.progress = .built count := rfl
    have postSample := storedDestination_built after source count adopted adoptedPresent adoptedBuilt
    have movedBacking := completedLandingState_named_backing layout state source ready.receiving count
      replacement ready.receivingDestination storage parentUpdate stored backing named present storedLookup built ordered parentDifferent
    have postBacking : StoredValueBacking layout after { stored with start := ready.receivingDestination.capability.start } :=
      storedValueBacking_tables layout _ after _ movedBacking rfl rfl
    have adoptedStorage : adopted.storage = replacement.storage := rfl
    have movedEq : { stored with start := ready.receivingDestination.capability.start } =
        ⟨adopted.storage, adopted.capability.start, adopted.capability.logicalType, count, some source, none, [], count⟩ := by
      rw [storedEq]
      rfl
    have sourceBacked : CarrierResultBacking layout after (.completed source) :=
      .completed source count adopted _ adoptedPresent adoptedBuilt postSample (by simpa only [movedEq] using postBacking)
    have channelFrame := completedLandingState_channel_frame state.construction source ready.receiving count
      replacement ready.receivingDestination storage parentUpdate
    have incomingInside : incoming < state.construction.destinations.size := by
      exact destinationCurrent_source_bound state.construction incoming ready.receiving ready.resolved
    have resolvedAfter : destinationCurrent result incoming = .ok source :=
      landingSuccessors_resolve state.construction result chain incoming ready.receiving source
        context.source.structural.2.1 channelFrame.1
        (by change chain.map (fun previous => (previous, source)) ++ _ = _; rw [channelFrame.2.1])
        incomingInside inside (exitLandingAnchor_chain_bounds _ _ _ _ _ _ _ _ _ selected)
        ready.resolved member
        (destinationSuccessorKeysInactive_built_terminal state.construction context.source.inactiveKeys source replacement present count built)
    have postReady : ReceivingCarrierLandingReady after incoming source :=
      ⟨source, adopted, adopted, resolvedAfter, adoptedPresent, adoptedPresent, .refl _, parentReady, Nat.le_refl _⟩
    refine ⟨after, ?_, sourceBacked, ⟨postReady⟩, channelFrame.2.2,
      .commit ready.receiving count replacement ready.receivingDestination storage parentUpdate chain ready.resolved
        present built ready.receivingPresent storedLookup (congrArg DestinationBacking.writeStorage sameBacking)
        ordered parentBound parentDifferent parentFootprint⟩
    have different : (ready.receiving != source) = true := by simp [current]
    simp only [landCarriersInto, List.length_cons, List.length_nil, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons,
      List.forIn_nil, receivingDestination, liftConstruction, ready.resolved, bind, pure,
      different, ↓reduceIte, landExitReplacementInto, committed]
    rfl

theorem landCarriersInto_completion_completed (layout : LayoutEnv) (origin : OriginId)
    (state : ExecutionState) (ambient : OwnershipAmbient)
    (token incoming selected source : Nat) (role : ExitReservationRole) (snapshot : PendingDestination)
    (context : OwnershipExecutionContext state ambient)
    (ticket : state.construction.exitReservations[token]? = some (.active role incoming selected snapshot))
    (backed : CarrierResultBacking layout state (.completed source))
    (ready : ReceivingCarrierLandingReady state selected source) :
    ∃ after, landCarriersInto origin [.completion token] [.completed source] state = .ok () after ∧
      CarrierResultBacking layout after (.completed source) ∧
      CarrierLandingReady after (.completion token) (.completed source) ∧
      CompletedCarrierLandingFrame state selected source after := by
  obtain ⟨after, landed, sourceBacking, ⟨postReady⟩, tickets, frame⟩ :=
    landCarriersInto_construct_completed layout origin state ambient selected source context backed ready
  refine ⟨after, ?_, sourceBacking, .completion token incoming selected source role snapshot ?_ postReady, frame⟩
  · simpa only [landCarriersInto, List.length_cons, List.length_nil, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons,
      List.forIn_nil, EvalM.get, ticket, bind, pure] using landed
  · simpa only [tickets] using ticket

#print axioms landCarriersInto_construct_completed
#print axioms landCarriersInto_completion_completed

end Goose.Proofs.ExitExecution

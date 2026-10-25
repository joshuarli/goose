import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsCleanupRewire
import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsLandingAnchor

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

theorem protectedCleanupRewire_support_back (state : ConstructionState) (root final : DestinationId)
    (landed anchor finalRow : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (valid : DestinationLifecycleInvariant state) (earlier : root < final)
    (parents : ProtectedRewireParent state root update)
    (parentActive : ∀ id row, update = some (id, row) → ∃ original : PendingDestination,
      state.destinations[id]? = some original ∧ activeProgress original.progress = true)
    (finalPresent : state.destinations[final]? = some finalRow) (active : activeProgress finalRow.progress = true)
    (anchorPresent : state.destinations[root]? = some anchor) (sameUse : landed.use = anchor.use)
    (path : OwnershipReplacementPath state.destinations root final)
    (id : DestinationId) (supported : ReplacementSupported (protectedCleanupRewireState state root final landed update) id) :
    ReplacementSupported state id := by
  have inside := (Array.getElem?_eq_some_iff.mp finalPresent).1
  obtain ⟨uses, finalAfter⟩ := protectedCleanupRewire_reads state root final landed update valid inside earlier parents
  have finalSupported : ReplacementSupported state final := .active final finalRow finalPresent active
  have rootSupported := path.supported finalSupported
  induction supported with
  | active index row found live =>
      by_cases same : index = final
      · subst index
        exact finalSupported
      · cases update with
        | none =>
            have cleaned : (abandonRowsState (protectedRows state root final) state).destinations[index]? = some row := by
              simpa only [protectedCleanupRewireState, Array.set!_eq_setIfInBounds,
                Array.getElem?_setIfInBounds_ne (Ne.symm same)] using found
            exact .active index row (abandonRowsState_active_unchanged _ state index row cleaned live) live
        | some pair =>
            obtain ⟨parent, updated⟩ := pair
            by_cases sameParent : parent = index
            · subst index
              obtain ⟨original, present, active⟩ := parentActive parent updated rfl
              exact .active parent original present active
            · have cleaned : (abandonRowsState (protectedRows state root final) state).destinations[index]? = some row := by
                simpa only [protectedCleanupRewireState, Array.set!_eq_setIfInBounds,
                  Array.getElem?_setIfInBounds_ne sameParent,
                  Array.getElem?_setIfInBounds_ne (Ne.symm same)] using found
              exact .active index row (abandonRowsState_active_unchanged _ state index row cleaned live) live
  | parent index parent row found use supported ih =>
      by_cases same : index = final
      · subst index
        have equal := Option.some.inj (found.symm.trans finalAfter)
        subst row
        exact .parent root parent anchor anchorPresent (sameUse.symm.trans use) rootSupported
      · obtain ⟨original, originalPresent, originalUse⟩ := uses index row found same
        exact .parent index parent original originalPresent (originalUse.trans use) ih

end Goose.Proofs.ConstructionExecutionOwnership

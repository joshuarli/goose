import Goose.Proofs.ConstructionExitBorrowedNamedActivation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId VarId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem resultLocal_alias_exitSource (source : RuntimeActivation) (state : ExecutionState)
    (incoming : Nat) (localVar : VarId) (origin : OriginId) (root : RootInst) (stored : StoredValue)
    (current : destinationCurrent state.construction incoming = .ok incoming)
    (rooted : rootOf source localVar state = .ok root state)
    (value : state.objects.lookup root = some (.stored stored))
    (alias : stored.destination = some incoming) :
    exitSource source incoming (.resultLocal localVar origin) state = .ok .namedResult state := by
  simp only [exitSource, receivingDestination, liftConstruction, current, bind, rooted, EvalM.get, value, alias, beq_self_eq_true, ite_true, pure]

theorem selectCompletion_named_local_alias (source : RuntimeActivation) (state : ExecutionState)
    (token incoming : Nat) (snapshot : PendingDestination) (localVar : VarId) (origin : OriginId)
    (root : RootInst) (stored : StoredValue)
    (waiting : state.construction.exitReservations[token]? = some (.waiting incoming))
    (present : state.construction.destinations[incoming]? = some snapshot) (opened : snapshot.progress = .open 0)
    (current : destinationCurrent state.construction incoming = .ok incoming)
    (rooted : rootOf source localVar state = .ok root state)
    (value : state.objects.lookup root = some (.stored stored))
    (alias : stored.destination = some incoming) :
    selectCompletionChannel source (.resultLocal localVar origin) (.completion token) state =
      .ok (.construct incoming) { state with construction := { state.construction with
        exitReservations := state.construction.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) } } := by
  have selection := selectWaiting_named_open_direct state.construction token incoming snapshot waiting present opened current
  have sourceKind := resultLocal_alias_exitSource source state incoming localVar origin root stored current rooted value alias
  simp only [selectCompletionChannel, EvalM.get, waiting, bind, sourceKind, liftConstruction, selection, pure]

theorem named_activation_fresh_preimage (state : ConstructionState) (token incoming : Nat) (snapshot : PendingDestination)
    (index oldIncoming oldSelected : Nat) (oldSnapshot : PendingDestination)
    (ticket : (state.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot))[index]? =
      some (.active .fresh oldIncoming oldSelected oldSnapshot)) :
    state.exitReservations[index]? = some (.active .fresh oldIncoming oldSelected oldSnapshot) := by
  by_cases same : token = index
  · subst index
    by_cases inside : token < state.exitReservations.size
    · simp [Array.set!_eq_setIfInBounds, inside] at ticket
    · simp [Array.set!_eq_setIfInBounds, inside] at ticket ⊢
  · simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, same] using ticket

theorem named_open_activation_source (state : ConstructionState) (token incoming : Nat) (snapshot : PendingDestination)
    (waiting : state.exitReservations[token]? = some (.waiting incoming))
    (present : state.destinations[incoming]? = some snapshot) (opened : snapshot.progress = .open 0)
    (current : destinationCurrent state incoming = .ok incoming) (valid : OwnershipSourceState state) :
    OwnershipSourceState { state with exitReservations := state.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) } := by
  let after := { state with exitReservations := state.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) }
  have selected := selectWaiting_named_open_direct state token incoming snapshot waiting present opened current
  have lifecycle := selectWaitingExitDestination_reservation_lifecycle token .namedResult state valid.structural.1.1
  rw [selected] at lifecycle
  have freshBefore (index oldIncoming oldSelected : Nat) (oldSnapshot : PendingDestination)
      (ticket : after.exitReservations[index]? = some (.active .fresh oldIncoming oldSelected oldSnapshot)) :=
    named_activation_fresh_preimage state token incoming snapshot index oldIncoming oldSelected oldSnapshot ticket
  have aliases : LiveFreshReservationSuccessorRoles after := by
    intro index oldIncoming oldSelected node oldSnapshot row ticket path found
    exact valid.aliases index oldIncoming oldSelected node oldSnapshot row (freshBefore index oldIncoming oldSelected oldSnapshot ticket)
      (DestinationSuccessorPath.congr (before := after) (after := state) rfl path) found
  have resumption : ResumptionReservationRoles after := by
    intro key saved found index oldIncoming oldSelected oldSnapshot ticket resolved
    exact valid.resumptionRoles key saved found index oldIncoming oldSelected oldSnapshot
      (freshBefore index oldIncoming oldSelected oldSnapshot ticket)
      ((destinationCurrent_congr_tables state after rfl rfl oldSelected).symm.trans resolved)
  have links : ConstructionOwnershipLinks after := by
    refine ⟨lifecycle.1, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · exact valid.structural.1.2.1.2.1
    · intro index oldIncoming oldSelected oldSnapshot ticket
      exact valid.structural.1.2.1.2.2.1.1 index oldIncoming oldSelected oldSnapshot (freshBefore index oldIncoming oldSelected oldSnapshot ticket)
    · exact valid.structural.1.2.1.2.2.1.2
    · intro index oldIncoming oldSelected oldSnapshot ticket
      exact valid.structural.1.2.1.2.2.2.1 index oldIncoming oldSelected oldSnapshot (freshBefore index oldIncoming oldSelected oldSnapshot ticket)
    · intro index oldIncoming oldSelected oldSnapshot currentRow ticket
      exact valid.structural.1.2.1.2.2.2.2.1 index oldIncoming oldSelected oldSnapshot currentRow (freshBefore index oldIncoming oldSelected oldSnapshot ticket)
    · intro index oldIncoming oldSelected oldSnapshot ticket
      exact valid.structural.1.2.1.2.2.2.2.2.1 index oldIncoming oldSelected oldSnapshot (freshBefore index oldIncoming oldSelected oldSnapshot ticket)
    · exact valid.structural.1.2.1.2.2.2.2.2.2
  have authority : SupportedReplacementAuthority after := by
    intro id parent selectedRow found use supported
    exact valid.structural.1.2.2.1 id parent selectedRow found use (replacementSupported_congr_destinations after state rfl id supported)
  have backing : ResumptionBackingSources after := valid.structural.1.2.2.2.1
  have unsupported : UnsupportedResumptionKeys after := by
    intro id saved found supported
    exact valid.structural.1.2.2.2.2.1 id saved found (replacementSupported_congr_destinations after state rfl id supported)
  have currentRoles : LiveFreshReservationRoles after := liveFreshReservationSuccessorRoles_current after aliases
  have rawRoles : LiveFreshReservationRawRoles after := liveFreshReservationSuccessorRoles_raw after aliases
  exact ⟨⟨⟨lifecycle, links, authority, backing, unsupported, currentRoles⟩, valid.structural.2.1, rawRoles⟩,
    aliases, valid.inactiveKeys, resumption⟩

#print axioms named_open_activation_source
#print axioms resultLocal_alias_exitSource
#print axioms selectCompletion_named_local_alias

end Goose.Proofs.ConstructionAcceptedExecution

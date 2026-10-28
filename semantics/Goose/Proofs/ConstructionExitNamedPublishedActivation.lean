import Goose.Proofs.ConstructionExitNamedActivationContext
import Goose.Proofs.ConstructionExitByteLetAlias

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId VarId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem selectWaiting_named_published_direct (state : ConstructionState) (token incoming count : Nat)
    (snapshot : PendingDestination)
    (waiting : state.exitReservations[token]? = some (.waiting incoming))
    (present : state.destinations[incoming]? = some snapshot) (published : snapshot.progress = .published count)
    (current : destinationCurrent state incoming = .ok incoming) :
    selectWaitingExitDestination token .namedResult state = .ok incoming { state with
      exitReservations := state.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) } := by
  have renewal : renewReceivingDestination incoming state = .ok incoming state := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, present, published]
  simp only [selectWaitingExitDestination, ConstructionM.get, waiting, bind, prepareExitDestination_equation,
    show (ExitSource.namedResult == ExitSource.namedResult) = true from rfl, ↓reduceIte,
    renewal, lookupDestination_result, present, published, Bool.false_or, pure, ConstructionM.set]

theorem selectCompletion_named_published_alias (source : RuntimeActivation) (state : ExecutionState)
    (token incoming count : Nat) (snapshot : PendingDestination) (localVar : VarId) (origin : OriginId)
    (root : RootInst) (stored : StoredValue)
    (waiting : state.construction.exitReservations[token]? = some (.waiting incoming))
    (present : state.construction.destinations[incoming]? = some snapshot) (published : snapshot.progress = .published count)
    (current : destinationCurrent state.construction incoming = .ok incoming)
    (rooted : rootOf source localVar state = .ok root state)
    (value : state.objects.lookup root = some (.stored stored)) (alias : stored.destination = some incoming) :
    selectCompletionChannel source (.resultLocal localVar origin) (.completion token) state =
      .ok (.construct incoming) { state with construction := { state.construction with
        exitReservations := state.construction.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) } } := by
  have selection := selectWaiting_named_published_direct state.construction token incoming count snapshot waiting present published current
  have sourceKind := resultLocal_alias_exitSource source state incoming localVar origin root stored current rooted value alias
  simp only [selectCompletionChannel, EvalM.get, waiting, bind, sourceKind, liftConstruction, selection, pure]

theorem prepareNamedCarrierAt_published_fault (origin : OriginId) (state : ExecutionState)
    (token incoming count : Nat) (snapshot : PendingDestination) (stored : StoredValue)
    (ticket : state.construction.exitReservations[token]? = some (.active (.named .awaitingSource) incoming incoming snapshot))
    (present : state.construction.destinations[incoming]? = some snapshot) (published : snapshot.progress = .published count)
    (current : destinationCurrent state.construction incoming = .ok incoming)
    (alias : stored.destination = some incoming) :
    prepareNamedCarrierAt origin token incoming stored state = .stop (.fault .flow) state := by
  simp only [prepareNamedCarrierAt, receivingDestination, liftConstruction, current, bind, pure, EvalM.get,
    ticket, alias, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte, getDestination, present,
    published, fault, EvalM.stop]

theorem published_alias_select_then_prepare_fault (source : RuntimeActivation) (state : ExecutionState)
    (token incoming count : Nat) (snapshot : PendingDestination) (localVar : VarId) (origin : OriginId)
    (root : RootInst) (stored : StoredValue)
    (waiting : state.construction.exitReservations[token]? = some (.waiting incoming))
    (present : state.construction.destinations[incoming]? = some snapshot) (published : snapshot.progress = .published count)
    (current : destinationCurrent state.construction incoming = .ok incoming)
    (rooted : rootOf source localVar state = .ok root state)
    (value : state.objects.lookup root = some (.stored stored)) (alias : stored.destination = some incoming) :
    ∃ activated, selectCompletionChannel source (.resultLocal localVar origin) (.completion token) state = .ok (.construct incoming) activated ∧
      prepareNamedCarrierAt origin token incoming stored activated = .stop (.fault .flow) activated := by
  let activated := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) } }
  have selected := selectCompletion_named_published_alias source state token incoming count snapshot localVar origin root stored waiting present published current rooted value alias
  have inside := (Array.getElem?_eq_some_iff.mp waiting).1
  have active : activated.construction.exitReservations[token]? = some (.active (.named .awaitingSource) incoming incoming snapshot) := by
    simp [activated, Array.set!_eq_setIfInBounds, inside]
  have currentAfter : destinationCurrent activated.construction incoming = .ok incoming :=
    (destinationCurrent_congr_tables state.construction activated.construction rfl rfl incoming).trans current
  exact ⟨activated, selected, prepareNamedCarrierAt_published_fault origin activated token incoming count snapshot stored active present published currentAfter alias⟩

#print axioms published_alias_select_then_prepare_fault
#print axioms prepareNamedCarrierAt_published_fault
#print axioms selectWaiting_named_published_direct
#print axioms selectCompletion_named_published_alias

end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Construct.Eval
import Goose.Proofs.ConstructionExecutionProtocolQueries

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct
open Goose.Core (DestinationId OriginId VarId)

theorem exitChannels_single_named_reuses_destination (state : ExecutionState)
    (source activation : RuntimeActivation) (id : DestinationId) (localVar : VarId)
    (origin operandOrigin : OriginId) (destination : PendingDestination)
    (descriptor : LocalVar) (scope scopeInst : Nat) (stored : StoredValue)
    (channel : activation.channels = [.construct id])
    (present : state.construction.destinations[id]? = some destination)
    (localPresent : source.vars[localVar]? = some descriptor)
    (scopePresent : source.scopes.find? (fun entry => entry.1 == descriptor.scope) = some (scope, scopeInst))
    (objectPresent : state.objects.lookup (.local source.act scopeInst localVar) = some (.stored stored))
    (alias : stored.destination = some id)
    (inside : id < state.construction.destinations.size)
    (unaliased : state.construction.destinationSuccessors.lookup id = none)
    (reservations : state.construction.exitReservations = #[])
    (built : ∃ count, destination.progress = .built count) :
    exitChannels source activation [.resultLocal localVar operandOrigin] origin state =
      .ok [.construct id] { state with construction := { state.construction with
        exitReservations := #[.active (.named .awaitingSource) id id destination] } } := by
  obtain ⟨count, built⟩ := built
  simp [exitChannels, exitSource, prepareExitDestination_equation, channel, rootOf, present, localPresent, scopePresent,
    objectPresent, alias, receivingDestination, reserveExitDestination,
    renewReceivingDestination, restoreNamedDestination,
    destinationCurrent_unaliased _ _ inside unaliased,
    lookupDestination_result, reservations, built,
    liftConstruction, ConstructionM.get, ConstructionM.set,
    EvalM.get, bind, pure, List.mapM_cons, List.mapM_nil]

private theorem reserveFresh (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination)
    (present : state.destinations[id]? = some destination)
    (fresh : destination.progress = .open 0)
    (inside : id < state.destinations.size)
    (unaliased : state.destinationSuccessors.lookup id = none) :
    reserveExitDestination id .newValue state =
      .ok (state.exitReservations.size, id) { state with
        exitReservations := state.exitReservations.push (.active .fresh id id destination) } := by
  simp [reserveExitDestination, prepareExitDestination_equation, renewReceivingDestination,
    destinationCurrent_unaliased _ _ inside unaliased,
    lookupDestination_result, present, fresh, exitFrontier_open _ _ _ _ _ present fresh,
    ConstructionM.get, ConstructionM.set, bind, pure]

set_option maxHeartbeats 1000000 in
theorem exitChannels_single_fresh_reuses_destination (state : ExecutionState)
    (source activation : RuntimeActivation) (id : DestinationId) (origin : OriginId)
    (operand : Expr) (destination : PendingDestination)
    (channel : activation.channels = [.construct id])
    (present : state.construction.destinations[id]? = some destination)
    (fresh : destination.progress = .open 0)
    (ordinary : ∀ localVar operandOrigin, operand ≠ .resultLocal localVar operandOrigin)
    (inside : id < state.construction.destinations.size)
    (unaliased : state.construction.destinationSuccessors.lookup id = none) :
    exitChannels source activation [operand] origin state =
      .ok [.construct id] { state with construction := { state.construction with
        exitReservations := state.construction.exitReservations.push (.active .fresh id id destination) } } := by
  cases operand <;>
    simp_all [exitChannels, exitSource, receivingDestination,
      destinationCurrent_unaliased _ _ inside unaliased,
      reserveFresh state.construction id destination present fresh inside unaliased,
      liftConstruction, bind, pure, List.mapM_cons, List.mapM_nil]

theorem completedDestination_retains_built_identity (state : ExecutionState)
    (id : DestinationId) (destination : PendingDestination) (count : Nat)
    (present : state.construction.destinations[id]? = some destination)
    (built : destination.progress = .built count) :
    completedDestination id state = .ok id state := by
  simp [completedDestination, getDestination, present, built, EvalM.get, bind, pure]

end Goose.Proofs.ConstructionExecutionOwnership

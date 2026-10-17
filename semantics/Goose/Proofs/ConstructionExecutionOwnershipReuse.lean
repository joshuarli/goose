import Goose.Proofs.ConstructionExecutionOwnershipNamed
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
    (alias : stored.destination = some id) :
    exitChannels source activation [.resultLocal localVar operandOrigin] origin state =
      .ok [.construct id] state := by
  simp [exitChannels, channel, getDestination, rootOf, present, localPresent, scopePresent,
    objectPresent, alias, EvalM.get, bind, pure, List.mapM_cons, List.mapM_nil]

set_option maxHeartbeats 1000000 in
theorem exitChannels_single_fresh_reuses_destination (state : ExecutionState)
    (source activation : RuntimeActivation) (id : DestinationId) (origin : OriginId)
    (operand : Expr) (destination : PendingDestination)
    (channel : activation.channels = [.construct id])
    (present : state.construction.destinations[id]? = some destination)
    (fresh : destination.progress = .open 0)
    (ordinary : ∀ localVar operandOrigin, operand ≠ .resultLocal localVar operandOrigin) :
    exitChannels source activation [operand] origin state = .ok [.construct id] state := by
  cases operand <;>
    simp_all [exitChannels, channel, getDestination, present, fresh, EvalM.get, bind, pure, List.mapM_cons, List.mapM_nil]

theorem completedDestination_retains_built_identity (state : ExecutionState)
    (id : DestinationId) (destination : PendingDestination) (count : Nat)
    (present : state.construction.destinations[id]? = some destination)
    (built : destination.progress = .built count) :
    completedDestination id state = .ok id state := by
  simp [completedDestination, getDestination, present, built, EvalM.get, bind, pure]

end Goose.Proofs.ConstructionExecutionOwnership

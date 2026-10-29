import Goose.Proofs.ConstructionExitNewestLeaf
import Goose.Proofs.ConstructionAcceptedAllocation
import Goose.Proofs.ConstructionExitDirectByteSetup

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionExecutionProtocol

theorem newDestination_newest_receiver (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : OriginId)
    (knownCount : Option Nat) (before after : ExecutionState) (id : Nat)
    (executed : newDestination layout owner ty request origin none knownCount before = .ok id after) :
    after.construction.destinations.size = id + 1 ∧
      ∃ row, after.construction.destinations[id]? = some row ∧ row.use = .receiver := by
  let prepared : ExecutionState := { before with construction :=
    { before.construction with storage := before.construction.storage.push ⟨ByteArray.empty, 0⟩ } }
  have query := stateQuery_receivingLayout layout ty prepared
  simp only [newDestination, liftConstruction, reserveStorage, ConstructionM.get,
    ConstructionM.set, bind, pure] at executed
  change ((receivingLayout layout ty >>= fun selected => liftConstruction origin
    (openDestination before.construction.storage.size
      ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount)) prepared) = .ok id after at executed
  cases result : receivingLayout layout ty prepared with
  | ok selected middle =>
      simp only [result, Goose.Proofs.Exit.stepState] at query
      subst middle
      simp only [bind, result, liftConstruction] at executed
      cases opened : openDestination before.construction.storage.size
          ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount prepared.construction with
      | fault reason final => simp only [opened] at executed; cases executed
      | ok value final =>
          simp only [opened] at executed
          cases executed
          obtain ⟨same, _, size, row⟩ := Goose.Proofs.ExitExecution.openDestination_receiver_row
            prepared.construction final _ _ _ _ id opened
          exact ⟨by simpa only [same] using size, row⟩
  | stop reason middle | escape target carriers middle | jump target kind middle =>
      simp only [bind, result] at executed
      cases executed

theorem newDestination_active_leaf (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : OriginId)
    (knownCount : Option Nat) (before after : ExecutionState) (id : Nat) (row : PendingDestination)
    (executed : newDestination layout owner ty request origin none knownCount before = .ok id after)
    (present : after.construction.destinations[id]? = some row)
    (active : Goose.Proofs.ConstructionExecutionOwnership.activeRow row = true)
    (lifecycle : ReservationLifecycleInvariant after.construction) :
    row.use = .receiver ∧ Goose.Proofs.ConstructionExecutionOwnership.treeRows after.construction id = [row] := by
  obtain ⟨newest, foundRow, found, receiver⟩ := newDestination_newest_receiver layout owner ty request origin knownCount before after id executed
  have same : foundRow = row := Option.some.inj (found.symm.trans present)
  subst foundRow
  exact ⟨receiver, newest_active_destination_is_leaf after.construction id row present active newest lifecycle.1.2.1 lifecycle.1.2.2.2⟩

#print axioms newDestination_newest_receiver
#print axioms newDestination_active_leaf

end Goose.Proofs.ConstructionAcceptedExecution

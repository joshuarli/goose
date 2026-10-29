import Goose.Proofs.ConstructionExitFreshCancelRoots
import Goose.Proofs.ConstructionExitMixedCancellation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem allocated_byte_exit_cancel_rooted (config : EvalConfig) (initialized : Nat) (owner : ActId)
    (origin : OriginId) (knownCount : Option Nat) (source target : RuntimeActivation) (bytes : List UInt8)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout owner (.varr (.int .u8)) .value origin none knownCount before = .ok id allocated)
    (channels : target.channels = [.construct id]) :
    ∃ prepared final,
      exitChannels source target [.bytes (.varr (.int .u8)) bytes origin] origin allocated = .ok [.construct id] prepared ∧
      exitChannelCleanupBorrowed origin [] [allocated.construction.exitReservations.size] true [] prepared = .ok () final ∧
      RootedBackingObservations config.layout final live (storageExtent before) := by
  obtain ⟨reserved, final, reserve, cancelled, rooted⟩ := allocated_receiver_cancel_rooted config initialized owner
    (.varr (.int .u8)) (.int .u8) .value origin knownCount before allocated id ambient types live regions pending world rfl created
  obtain ⟨⟨backing⟩, _⟩ := newDestination_open_ready config initialized owner (.varr (.int .u8)) .value origin knownCount
    before allocated ambient types live regions pending id (.int .u8) world rfl created
  have current := newDestination_current_self config initialized owner (.varr (.int .u8)) .value origin knownCount before allocated id
    ambient types live regions pending world created
  have setup := (direct_byte_exit_setup source target bytes origin allocated id backing.destination channels backing.present backing.opened current).1
  have equal : reserved = { allocated.construction with
      exitReservations := allocated.construction.exitReservations.push (.active .fresh id id backing.destination) } := by
    exact (ConstructionResult.ok.inj (reserve.symm.trans (reserve_open_zero_direct allocated.construction id backing.destination
      backing.present backing.opened current))).2
  let prepared := { allocated with construction := reserved }
  have actualSetup : exitChannels source target [.bytes (.varr (.int .u8)) bytes origin] origin allocated =
      .ok [.construct id] prepared := by simpa only [prepared, equal] using setup
  have lifted : (do
      liftConstruction origin (cancelExitReservation allocated.construction.exitReservations.size [])
      liftConstruction origin (releaseExitReservation allocated.construction.exitReservations.size)) prepared =
        .ok () { allocated with construction := final } := by
    rw [liftConstruction_sequence]
    simp [liftConstruction, prepared, cancelled]
  refine ⟨prepared, { allocated with construction := final }, actualSetup, ?_, rooted⟩
  simp only [exitChannelCleanupBorrowed, Bool.true_eq, ↓reduceIte, List.reverse_cons, List.reverse_nil,
    List.forIn_cons, List.forIn_nil, List.filterMap_nil, bind, pure] at lifted ⊢
  cases first : liftConstruction origin (cancelExitReservation allocated.construction.exitReservations.size []) prepared with
  | stop reason state | escape reason carriers state | jump reason kind state => simp [first] at lifted
  | ok value middle =>
    simp only [first] at lifted ⊢
    cases second : liftConstruction origin (releaseExitReservation allocated.construction.exitReservations.size) middle with
    | stop reason state | escape reason carriers state | jump reason kind state => simp [second] at lifted
    | ok value state =>
      simp [second] at lifted
      simp [bind, pure, first, second, lifted]

#print axioms allocated_byte_exit_cancel_rooted

end Goose.Proofs.ConstructionAcceptedExecution

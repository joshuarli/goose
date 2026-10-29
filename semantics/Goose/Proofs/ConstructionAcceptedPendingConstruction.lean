import Goose.Proofs.ConstructionExitWaitingCarrier

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ExitExecution

theorem CarriersLandingReady.of_construction_eq {before after : ExecutionState} {channels : List Channel} {carriers : List Carrier}
    (same : after.construction = before.construction) (valid : CarriersLandingReady before channels carriers) :
    CarriersLandingReady after channels carriers := by
  have receiving (incoming source : Nat) (ready : ReceivingCarrierLandingReady before incoming source) :
      ReceivingCarrierLandingReady after incoming source := by
    refine ⟨ready.receiving, ready.sourceDestination, ready.receivingDestination, ?_, ?_, ?_, ?_, ?_, ready.ordered⟩
    · simpa only [same] using ready.resolved
    · simpa only [same] using ready.sourcePresent
    · simpa only [same] using ready.receivingPresent
    · simpa only [same] using ready.path
    · simpa only [same] using ready.parent
  refine ⟨valid.lengths, ?_⟩
  intro channel carrier member
  have ready := valid.pairs channel carrier member
  cases ready with
  | register ty value => exact .register ty value
  | construct incoming source ready => exact .construct incoming source (receiving incoming source ready)
  | completion token incoming selected source role snapshot ticket ready =>
    exact .completion token incoming selected source role snapshot (by simpa only [same] using ticket) (receiving selected source ready)
  | pendingNamed token incoming selected snapshot ticket =>
    exact .pendingNamed token incoming selected snapshot (by simpa only [same] using ticket)

theorem CarrierResultBacking.of_construction_eq {before after : ExecutionState} {layout : LayoutEnv} {carrier : Carrier}
    (same : after.construction = before.construction) (valid : CarrierResultBacking layout before carrier) :
    CarrierResultBacking layout after carrier := by
  have sample (id : Nat) (stored : StoredValue) (prior : storedDestination id before = .ok stored before) :
      storedDestination id after = .ok stored after := by
    cases found : before.construction.destinations[id]? with
    | none => simp [storedDestination, getDestination, EvalM.get, found, bind, fault, EvalM.stop] at prior
    | some row =>
      cases phase : progressCount row.progress with
      | none => simp [storedDestination, getDestination, EvalM.get, found, bind, pure, phase, fault, EvalM.stop] at prior
      | some count =>
        simp [storedDestination, getDestination, EvalM.get, same, found, bind, phase, pure] at prior ⊢
        exact prior
  cases valid with
  | register value backed => exact .register value (backed.construction_frame same)
  | completed id count row stored present built sampled backed =>
    exact .completed id count row stored (by simpa only [same] using present) built (sample id stored sampled)
      (backed.construction_frame same)
  | pendingNamed token incoming selected count snapshot row stored ticket present marked phase sampled backed =>
    exact .pendingNamed token incoming selected count snapshot row stored (by simpa only [same] using ticket)
      (by simpa only [same] using present) marked phase (sample selected stored sampled) (backed.construction_frame same)

#print axioms CarriersLandingReady.of_construction_eq
#print axioms CarrierResultBacking.of_construction_eq
end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionExitByteAnchors
import Goose.Proofs.ConstructionExitByteReady
import Goose.Proofs.ExitExecutionLiveCarrierLanding
import Goose.Proofs.ExitExecutionLandingMetadata
import Goose.Proofs.ExitExecutionLandingActivationFilter
import Goose.Proofs.ExitExecutionLandingRuntimeReplay
import Goose.Proofs.ConstructionExitByteAdaptation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem reserved_byte_finish_channels_caller (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (reservationBefore reserved : ConstructionState) (incoming selected token count writeCount : Nat)
    (receiverState : ExecutionState) (receiverConstruction : receiverState.construction = reservationBefore)
    (receiver : OpenDestinationBacking config.layout receiverState incoming (.varr (.int .u8)) (count + 1))
    (receiverRole : receiver.destination.use = .receiver)
    (receiverAdaptation : receiver.destination.adaptation = none)
    (receiverPhysical : receiver.destination.capability.layout = .varr (.int .u8))
    (receiverCurrent : destinationCurrent reservationBefore incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue reservationBefore = .ok (token, selected) reserved)
    (environment : RuntimeActivation) (before after : ExecutionState) (construction : before.construction = reserved)
    (ambient : OwnershipAmbient) (channels : List Channel) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before (.exitChannels [token] channels [.completed selected] :: ambient) types live regions pending)
    (ready : OpenDestinationBacking config.layout before selected (.varr (.int .u8)) writeCount)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (bytes : List UInt8) (fits : writeCount + bytes.length < 2 ^ 32)
    (selectedCurrent : destinationCurrent before.construction selected = .ok selected)
    (origin : Goose.Core.OriginId)
    (built : buildExpr (fuel + 1) config environment selected (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after)
    (scope : Nat) (scopeInst : Goose.Core.ScopeInst) (unwindInner caller : RuntimeActivation)
    (callerScope : Nat) (callerScopeInst : Goose.Core.ScopeInst) (innerAct handlerAct : Nat) :
    ∃ cleaned landed,
      exitChannelCleanupBorrowed origin [] [token] false [.completed selected] after = .ok () cleaned ∧
      let unwound := releaseScopeState unwindInner scope scopeInst cleaned
      let crossed := { unwound with activations := unwound.activations.filter (fun current => current.act != innerAct) }
      let callerUnwound := releaseScopeState caller callerScope callerScopeInst crossed
      finishChannels config.layout [.construct incoming] [.varr (.int .u8)] [.completed selected] origin
        { callerUnwound with activations := callerUnwound.activations.filter (fun current => current.act != handlerAct) } = .ok () landed := by
  have receiverPresent : reservationBefore.destinations[incoming]? = some receiver.destination := by
    simpa only [receiverConstruction] using receiver.present
  have reserveFacts := reserve_open_receiver_snapshot reservationBefore reserved incoming selected token count receiver.destination
    receiverPresent receiver.opened receiverCurrent reservation
  have ticket : before.construction.exitReservations[token]? = some (.active .fresh incoming selected receiver.destination) := by
    simpa only [construction] using reserveFacts.2
  obtain ⟨cleaned, cleanup, context⟩ := build_packed_bytes_cleanup_context fuel config environment selected writeCount token incoming
    receiver.destination bytes origin before after channels [.completed selected] ambient world.ownership ticket ready packed request selectedCurrent built scope scopeInst
  have tickets := buildExpr_bytes_tickets fuel config environment selected (.varr (.int .u8)) bytes origin before after
    ready.destination writeCount world.ownership.source selectedCurrent ready.present ready.opened built
  have afterTicket : after.construction.exitReservations[token]? = some (.active .fresh incoming selected receiver.destination) := by
    simpa only [tickets] using ticket
  have released := releaseExitReservation_active after.construction token .fresh incoming selected receiver.destination afterTicket
  have exactCleanup : exitChannelCleanupBorrowed origin [] [token] false [.completed selected] after =
      .ok () { after with construction := { after.construction with
        exitReservations := after.construction.exitReservations.set! token .released } } := by
    simp only [exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.forIn_cons, List.forIn_nil,
      liftConstruction, released, bind, pure]
  have equal := cleanup.symm.trans exactCleanup
  cases equal
  obtain ⟨⟨landingReady⟩, backed⟩ := reserved_byte_landing_ready fuel config initialized reservationBefore reserved incoming selected token count writeCount
    receiverState receiverConstruction receiver receiverRole receiverCurrent reservation environment before after construction
    (.exitChannels [token] channels [.completed selected] :: ambient) types live regions pending world ready packed request bytes fits selectedCurrent origin built scope scopeInst
  let state := releaseScopeState environment scope scopeInst { after with construction := { after.construction with
    exitReservations := after.construction.exitReservations.set! token .released } }
  have receiverCurrentAfter := reserved_byte_receiver_current fuel config reservationBefore reserved incoming selected token count writeCount
    receiver.destination receiverPresent receiver.opened receiverCurrent reservation environment before after construction world.ownership.source
    ready packed request selectedCurrent bytes origin built scope scopeInst
  have receiverParent := reserved_parent_survives_byte_build fuel config reservationBefore reserved incoming selected token count writeCount
    receiver.destination receiverPresent receiver.opened receiverCurrent reservation environment before after construction world.ownership.source
    ready packed request selectedCurrent bytes origin built scope scopeInst
  have initialReceiver : before.construction.destinations[incoming]? = some
      { receiver.destination with progress := .exiting (count + 1) selected } := by
    simpa only [construction] using reserveFacts.1
  have distinct : incoming ≠ selected := by
    intro same
    have sameRow : { receiver.destination with progress := .exiting (count + 1) selected } = ready.destination := by
      apply Option.some.inj
      have found : before.construction.destinations[incoming]? = some ready.destination := by
        simpa only [same] using ready.present
      exact initialReceiver.symm.trans found
    have impossible := congrArg PendingDestination.progress sameRow
    simp only [ready.opened] at impossible
    cases impossible
  obtain ⟨replacement, replacementPresent, capability, phase⟩ := build_packed_bytes_capability fuel config environment selected writeCount
    bytes origin before after world.ownership.source ready packed request selectedCurrent built
  obtain ⟨adaptedRow, adaptedPresent, adaptationEq, _⟩ := build_packed_bytes_adaptation fuel config environment selected writeCount
    bytes origin before after world.ownership.source ready packed request selectedCurrent built
  have sameRow : adaptedRow = replacement := Option.some.inj (adaptedPresent.symm.trans replacementPresent)
  have adaptationBefore : ready.destination.adaptation = none := by
    have receiverStored : reservationBefore.storage[receiver.destination.storage]? = some receiver.storage := by
      simpa only [receiverConstruction] using receiver.bytes
    obtain ⟨reservedRow, found, physical, adaptation⟩ := reserve_open_replacement_metadata reservationBefore reserved incoming selected token count
      receiver.destination receiver.storage receiverPresent receiver.opened receiverStored receiverCurrent reservation
    have same : reservedRow = ready.destination := Option.some.inj (found.symm.trans (by simpa only [construction] using ready.present))
    simpa only [same, receiverAdaptation] using adaptation
  have physicalBefore : ready.destination.capability.layout = .varr (.int .u8) := by
    have receiverStored : reservationBefore.storage[receiver.destination.storage]? = some receiver.storage := by
      simpa only [receiverConstruction] using receiver.bytes
    obtain ⟨reservedRow, found, physical, adaptation⟩ := reserve_open_replacement_metadata reservationBefore reserved incoming selected token count
      receiver.destination receiver.storage receiverPresent receiver.opened receiverStored receiverCurrent reservation
    have same : reservedRow = ready.destination := Option.some.inj (found.symm.trans (by simpa only [construction] using ready.present))
    simpa only [same, receiverPhysical] using physical
  have finalAdapt : replacement.adaptation = none := by simpa only [sameRow, adaptationBefore] using adaptationEq
  have finalPhysical : replacement.capability.layout = .varr (.int .u8) := by simpa only [capability, physicalBefore]
  have finalLogical : replacement.capability.logicalType = .varr (.int .u8) := by simpa only [capability] using ready.logicalType
  let innerUnwound := releaseScopeState unwindInner scope scopeInst { after with construction := { after.construction with
    exitReservations := after.construction.exitReservations.set! token .released } }
  let crossed := { innerUnwound with activations := innerUnwound.activations.filter (fun current => current.act != innerAct) }
  let callerUnwound := releaseScopeState caller callerScope callerScopeInst crossed
  let alternate := { callerUnwound with activations := callerUnwound.activations.filter (fun current => current.act != handlerAct) }
  obtain ⟨landed, finished⟩ := land_constructed_byte_finishes_replay config.layout origin state alternate
    (.returned [.completed selected] :: ambient) incoming selected (writeCount + bytes.length)
    { receiver.destination with progress := .exiting (count + 1) selected } replacement rfl context backed landingReady
    receiverCurrentAfter distinct receiverParent receiverRole replacementPresent phase finalAdapt finalPhysical finalLogical
  exact ⟨_, landed, cleanup, finished⟩

#print axioms reserved_byte_finish_channels_caller

end Goose.Proofs.ConstructionAcceptedExecution

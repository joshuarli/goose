import Goose.Proofs.ConstructionExitByteCapability
import Goose.Proofs.ConstructionExitReceiverParent
import Goose.Proofs.ConstructionExitByteSetup

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem reserved_byte_landing_ready (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (reservationBefore reserved : ConstructionState) (incoming selected token count writeCount : Nat)
    (receiverState : ExecutionState) (receiverConstruction : receiverState.construction = reservationBefore)
    (receiver : OpenDestinationBacking config.layout receiverState incoming (.varr (.int .u8)) (count + 1))
    (receiverRole : receiver.destination.use = .receiver)
    (receiverCurrent : destinationCurrent reservationBefore incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue reservationBefore = .ok (token, selected) reserved)
    (environment : RuntimeActivation) (before after : ExecutionState) (construction : before.construction = reserved)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (ready : OpenDestinationBacking config.layout before selected (.varr (.int .u8)) writeCount)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (bytes : List UInt8) (fits : writeCount + bytes.length < 2 ^ 32)
    (selectedCurrent : destinationCurrent before.construction selected = .ok selected)
    (origin : Goose.Core.OriginId)
    (built : buildExpr (fuel + 1) config environment selected (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after)
    (scope : Nat) (scopeInst : Goose.Core.ScopeInst) :
    let cleaned := { after with construction := { after.construction with
      exitReservations := after.construction.exitReservations.set! token .released } }
    let unwound := releaseScopeState environment scope scopeInst cleaned
    Nonempty (ReceivingCarrierLandingReady unwound incoming selected) ∧
      CarrierResultBacking config.layout unwound (.completed selected) := by
  have receiverPresent : reservationBefore.destinations[incoming]? = some receiver.destination := by
    simpa only [receiverConstruction] using receiver.present
  have parent := reserved_byte_receiver_parent fuel config reservationBefore reserved incoming selected token count writeCount
    receiver.destination receiverPresent receiver.opened receiverRole receiverCurrent reservation environment before after construction
    world.ownership.source ready packed request selectedCurrent bytes origin built scope scopeInst
  obtain ⟨result, resultPresent, order⟩ := reserved_byte_built_start_order fuel config reservationBefore reserved incoming selected token count writeCount
    receiverState receiverConstruction receiver receiverCurrent reservation environment before after construction world.ownership.source
    ready packed request selectedCurrent bytes origin built
  have initially := (reserve_open_receiver_snapshot reservationBefore reserved incoming selected token count receiver.destination
    receiverPresent receiver.opened receiverCurrent reservation)
  have tokenBefore : before.construction.exitReservations[token]? = some (.active .fresh incoming selected receiver.destination) := by
    simpa only [construction] using initially.2
  have distinct : selected ≠ incoming := by
    intro equal
    have same : { receiver.destination with progress := .exiting (count + 1) selected } = ready.destination := by
      apply Option.some.inj
      have found := initially.1
      rw [← construction] at found
      have selectedFound : before.construction.destinations[incoming]? = some ready.destination := by
        simpa only [equal] using ready.present
      exact found.symm.trans selectedFound
    have impossible := congrArg PendingDestination.progress same
    simp only [ready.opened] at impossible
    cases impossible
  have receiverId : receiver.destination.capability.id = incoming := by
    have indexed := world.ownership.source.structural.1.1.1.2.1 incoming
      { receiver.destination with progress := .exiting (count + 1) selected }
      (by simpa only [construction] using initially.1)
    exact indexed
  have roles := world.ownership.source.aliases token incoming selected selected receiver.destination ready.destination tokenBefore
    (.refl selected) ready.present
  simp only [receiverId, if_neg distinct] at roles
  obtain ⟨actual, storage, actualPresent, _, _, _, _, _, use, _, _⟩ :=
    buildExpr_byteOwner_geometry fuel config environment bytes origin selected writeCount before after ready packed request fits
      world.ownership.source.structural.1.1.1 selectedCurrent built
  have sameResult : actual = result := Option.some.inj (actualPresent.symm.trans resultPresent)
  have resultUse : result.use = .replacement incoming := by rw [← sameResult, use]; exact roles.1
  have backed := accepted_byte_return_carrier_backed fuel config initialized environment bytes origin selected writeCount
    before after ambient types live regions pending world ready packed request fits selectedCurrent built
  refine ⟨⟨⟨incoming, result, { receiver.destination with progress := .exiting (count + 1) selected },
    parent.1, resultPresent, parent.2.1, .step selected incoming incoming result resultPresent resultUse (.refl _),
    parent.2.2, order⟩⟩, completed_carrier_after_cleanup_unwind config.layout after token selected environment scope scopeInst backed⟩

#print axioms reserved_byte_landing_ready

end Goose.Proofs.ConstructionAcceptedExecution

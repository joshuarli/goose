import Goose.Proofs.ConstructionAcceptedByteReturnCompletion
import Goose.Proofs.ConstructionExitReleaseWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem withCompletion_byteReceiver_separated_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized before ambient types live regions [])
    (history : ReservationReferencesBounded before.construction ambient)
    (separated : ∀ retained ∈ completedCarrierIds ambient.retained,
      destinationDescendant before.construction.destinations id retained = false)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    ∃ after,
      withCompletionChannels [.construct id] origin
        (fun channels => evalProduce (fuel + 2) config environment channels (.bytes (.varr (.int .u8)) bytes origin)) before =
          .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.returned [.completed id] :: ambient) types live regions
        [⟨[.construct id], [.completed id]⟩] ∧
      after = { before with construction := after.construction } ∧
      (ready.destination.capability.layout = .varr (.int .u8) →
        Nonempty (NormalizedCompletedCarrier after (.varr (.int .u8)) id)) ∧
      (∀ storageId, ready.destination.capability.layout = .varr (.int .u8) →
        ready.destination.backing = .direct storageId → Nonempty (BuiltByteReceiver config.layout after id storageId bytes.length)) := by
  let token := before.construction.exitReservations.size
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting id) } }
  obtain ⟨built, produced, builtWorld, ticket, targetReady, targetBacked, outer, normalized, geometry⟩ := completion_byteReceiver_separated_world fuel config initialized environment id bytes origin
    before ambient types live regions world history separated ready packed adaptation receiver request current fits mutable cutoff covered
  obtain ⟨after, cleanup, afterWorld⟩ := exit_cleanup_returned_world config initialized built token id id ready.destination [] [.construct id] [.completed id]
    ambient types live regions [] origin ticket builtWorld (by intro frame member; cases member) (by simp) targetReady targetBacked
  have produced' : evalProduce (fuel + 2) config environment [.completion token] (.bytes (.varr (.int .u8)) bytes origin) waited =
      .ok [.completed id] built := produced
  have setup : completionChannelSetup [.construct id] origin before = .ok ([.completion token], [token]) waited := by
    simp [completionChannelSetup, waitExitDestination, token, waited, liftConstruction, ConstructionM.get, ConstructionM.set, bind, pure]
  let final := { built with construction := { built.construction with
    exitReservations := built.construction.exitReservations.set! token .released } }
  have released := releaseExitReservation_active built.construction token .fresh id id ready.destination ticket
  have actualCleanup : exitChannelCleanupBorrowed origin [] [token] false [.completed id] built = .ok () final := by
    simp only [exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.forIn_cons, List.forIn_nil, liftConstruction, released, bind, pure]
    rfl
  have equal : after = final := (ExecutionStep.ok.inj (cleanup.symm.trans actualCleanup)).2
  subst after
  refine ⟨final, ?_, afterWorld, ?_, ?_, ?_⟩
  · simp [withCompletionChannels, setup, produced', materializeOwnedCarriers, List.mapM_cons, List.mapM_nil,
      List.forIn_cons, List.forIn_nil, liftConstruction, released, bind, pure, final]
  · cases before
    cases built
    simp_all only [final, ExecutionState.mk.injEq]
  · intro physical
    obtain ⟨valid⟩ := normalized physical
    refine ⟨⟨valid.destination, valid.present, valid.built, ?_, valid.adaptation, valid.normalized, valid.type, valid.constructible⟩⟩
    simpa only [destinationCanWrite_result, final] using valid.writable
  · intro storageId physical direct
    obtain ⟨facts⟩ := geometry storageId physical direct
    have valid := facts.normalized
    have validFinal : NormalizedCompletedCarrier final (.varr (.int .u8)) id := by
      refine ⟨valid.destination, valid.present, valid.built, ?_, valid.adaptation, valid.normalized, valid.type, valid.constructible⟩
      simpa only [destinationCanWrite_result, final] using valid.writable
    exact ⟨⟨facts.row, facts.storage, facts.present, facts.stored, facts.progress, facts.receiver, facts.backing,
      facts.storageEq, facts.packed, facts.request, facts.logical, facts.adaptation, facts.sampled, validFinal⟩⟩



theorem withCompletion_byteReceiver_geometry_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized before ambient types live regions [])
    (history : ReservationReferencesBounded before.construction ambient)
    (noRetained : completedCarrierIds ambient.retained = [])
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    ∃ after,
      withCompletionChannels [.construct id] origin
        (fun channels => evalProduce (fuel + 2) config environment channels (.bytes (.varr (.int .u8)) bytes origin)) before =
          .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.returned [.completed id] :: ambient) types live regions
        [⟨[.construct id], [.completed id]⟩] ∧
      after = { before with construction := after.construction } ∧
      (ready.destination.capability.layout = .varr (.int .u8) →
        Nonempty (NormalizedCompletedCarrier after (.varr (.int .u8)) id)) ∧
      (∀ storageId, ready.destination.capability.layout = .varr (.int .u8) →
        ready.destination.backing = .direct storageId → Nonempty (BuiltByteReceiver config.layout after id storageId bytes.length)) := by
  apply withCompletion_byteReceiver_separated_world fuel config initialized environment id bytes origin before ambient types live regions
    world history ?_ ready packed adaptation receiver request current fits mutable cutoff covered
  intro retained member
  rw [noRetained] at member
  cases member

theorem withCompletion_byteReceiver_normalized_observed_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized before ambient types live regions [])
    (history : ReservationReferencesBounded before.construction ambient)
    (noRetained : completedCarrierIds ambient.retained = [])
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    ∃ after,
      withCompletionChannels [.construct id] origin
        (fun channels => evalProduce (fuel + 2) config environment channels (.bytes (.varr (.int .u8)) bytes origin)) before =
          .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.returned [.completed id] :: ambient) types live regions
        [⟨[.construct id], [.completed id]⟩] ∧
      after = { before with construction := after.construction } ∧
      (ready.destination.capability.layout = .varr (.int .u8) →
        Nonempty (NormalizedCompletedCarrier after (.varr (.int .u8)) id)) := by
  obtain ⟨after, produced, afterWorld, outer, normalized, geometry⟩ :=
    withCompletion_byteReceiver_geometry_world fuel config initialized environment id bytes origin before ambient types live regions
      world history noRetained ready packed adaptation receiver request current fits mutable cutoff covered
  exact ⟨after, produced, afterWorld, outer, normalized⟩

theorem withCompletion_byteReceiver_observed_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized before ambient types live regions [])
    (history : ReservationReferencesBounded before.construction ambient)
    (noRetained : completedCarrierIds ambient.retained = [])
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    ∃ after,
      withCompletionChannels [.construct id] origin
        (fun channels => evalProduce (fuel + 2) config environment channels (.bytes (.varr (.int .u8)) bytes origin)) before =
          .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.returned [.completed id] :: ambient) types live regions
        [⟨[.construct id], [.completed id]⟩] ∧
      after = { before with construction := after.construction } := by
  obtain ⟨after, produced, afterWorld, outer, normalized⟩ :=
    withCompletion_byteReceiver_normalized_observed_world fuel config initialized environment id bytes origin before ambient types live regions
      world history noRetained ready packed adaptation receiver request current fits mutable cutoff covered
  exact ⟨after, produced, afterWorld, outer⟩

theorem withCompletion_byteReceiver_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized before ambient types live regions [])
    (history : ReservationReferencesBounded before.construction ambient)
    (noRetained : completedCarrierIds ambient.retained = [])
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    ∃ after,
      withCompletionChannels [.construct id] origin
        (fun channels => evalProduce (fuel + 2) config environment channels (.bytes (.varr (.int .u8)) bytes origin)) before =
          .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.returned [.completed id] :: ambient) types live regions
        [⟨[.construct id], [.completed id]⟩] := by
  obtain ⟨after, produced, afterWorld, outer⟩ :=
    withCompletion_byteReceiver_observed_world fuel config initialized environment id bytes origin before ambient types live regions
      world history noRetained ready packed adaptation receiver request current fits mutable cutoff covered
  exact ⟨after, produced, afterWorld⟩

#print axioms withCompletion_byteReceiver_world
#print axioms withCompletion_byteReceiver_observed_world
#print axioms withCompletion_byteReceiver_separated_world
#print axioms withCompletion_byteReceiver_geometry_world
#print axioms withCompletion_byteReceiver_normalized_observed_world
end Goose.Proofs.ConstructionAcceptedExecution

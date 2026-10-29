import Goose.Proofs.ConstructionAcceptedByteFinishCall
import Goose.Proofs.ConstructionAcceptedByteReturnComplete
import Goose.Proofs.ConstructionAcceptedChannelScopeExit
import Goose.Proofs.ConstructionAcceptedUnusedScope
import Goose.Proofs.ConstructionAcceptedEntryActivation
import Goose.Proofs.ConstructionAcceptedByteScopeObservations

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem byteBody_finish_world_separated (fuel deliveryFuel : Nat) (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (scope id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before boundState middle : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (channels : activation.channels = [.construct id])
    (bound : bindAll activation.act before.nextScope [] (ownershipResultScopeState activation scope before) = .ok () boundState)
    (normal : execStmts (fuel + 2) config { activation with scopes := (scope, before.nextScope) :: activation.scopes }
      [] boundState = .ok (.normal .unit) middle)
    (absent : ∀ descriptor ∈ activation.vars.toList, descriptor.scope ≠ scope)
    (world : AcceptedWorld config initialized middle (.callChannels activation [] :: ambient) types live regions [])
    (history : ReservationReferencesBounded middle.construction (.callChannels activation [] :: ambient))
    (separated : ∀ retained ∈ completedCarrierIds (OwnershipAmbient.retained (.callChannels activation [] :: ambient)),
      destinationDescendant middle.construction.destinations id retained = false)
    (ready : OpenDestinationBacking config.layout middle id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (physical : ready.destination.capability.layout = .varr (.int .u8))
    (current : destinationCurrent middle.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    ∃ after, (finishActivation config.layout activation [.varr (.int .u8)] origin
        (execActivationBody (fuel + 3) config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩) >>= fun carriers =>
        deliverCarriers deliveryFuel config.layout [.construct id] carriers origin) before = .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.returned [.completed id] :: ambient) types live regions
        [⟨[.construct id], [.completed id]⟩] ∧
      after.objects = middle.objects ∧ after.objectOrdinals = middle.objectOrdinals ∧
      after.nextAct = middle.nextAct ∧ after.nextScope = middle.nextScope ∧
      (∀ storageId, ready.destination.backing = .direct storageId →
        Nonempty (BuiltByteReceiver config.layout after id storageId bytes.length)) := by
  obtain ⟨built, produced, builtWorld, outer, normalized, geometry⟩ :=
    withCompletion_byteReceiver_separated_world fuel config initialized
      { activation with scopes := (scope, before.nextScope) :: activation.scopes } id bytes origin middle
      (.callChannels activation [] :: ambient) types live regions world history separated ready packed adaptation receiver request current fits mutable cutoff covered
  let released := releaseScopeState activation scope before.nextScope built
  have releasedWorld := builtWorld.releaseScope_withoutDeclarations config initialized built
    (.returned [.completed id] :: .callChannels activation [] :: ambient) types live regions
    [⟨[.construct id], [.completed id]⟩] activation scope before.nextScope absent
  obtain ⟨valid⟩ := normalized physical
  have releasedValid : NormalizedCompletedCarrier released (.varr (.int .u8)) id :=
    NormalizedCompletedCarrier.of_construction_eq (before := built) (after := released) rfl valid
  have body := execActivationBody_bound_channelTail (fuel + 2) config activation [] scope []
    (.bytes (.varr (.int .u8)) bytes origin) before boundState middle bound normal
  have done : execActivationBody (fuel + 3) config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩ before = .ok [.completed id] released := by
    simp only [channels, expressionOrigin] at body
    simp only [channels] at produced
    rw [produced] at body
    simpa [released, Nat.add_assoc] using body
  obtain ⟨finish, finalWorld⟩ := finishConstructSelfCall_world deliveryFuel config initialized activation id (.varr (.int .u8)) origin
    _ before released ambient types live regions [⟨[.construct id], [.completed id]⟩] channels done releasedWorld releasedValid
  have releasedObjects := releaseScope_withoutDeclarations_objects built activation scope before.nextScope absent
  refine ⟨_, finish, finalWorld, ?_, ?_, ?_, ?_, ?_⟩
  · have same : built.objects = middle.objects := by simpa only using congrArg ExecutionState.objects outer
    exact releasedObjects.1.trans same
  · have same : built.objectOrdinals = middle.objectOrdinals := by simpa only using congrArg ExecutionState.objectOrdinals outer
    exact releasedObjects.2.trans same
  · simpa only [released, releaseScopeState] using congrArg ExecutionState.nextAct outer
  · simpa only [released, releaseScopeState] using congrArg ExecutionState.nextScope outer
  · intro storageId direct
    obtain ⟨facts⟩ := geometry storageId physical direct
    exact ⟨BuiltByteReceiver.of_construction_eq (before := built)
      (after := { released with activations := released.activations.filter (fun current => current.act != activation.act) }) rfl facts⟩

theorem byteBody_finish_world_observed (fuel deliveryFuel : Nat) (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (scope id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before boundState middle : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (channels : activation.channels = [.construct id])
    (bound : bindAll activation.act before.nextScope [] (ownershipResultScopeState activation scope before) = .ok () boundState)
    (normal : execStmts (fuel + 2) config { activation with scopes := (scope, before.nextScope) :: activation.scopes }
      [] boundState = .ok (.normal .unit) middle)
    (absent : ∀ descriptor ∈ activation.vars.toList, descriptor.scope ≠ scope)
    (world : AcceptedWorld config initialized middle (.callChannels activation [] :: ambient) types live regions [])
    (history : ReservationReferencesBounded middle.construction (.callChannels activation [] :: ambient))
    (noRetained : completedCarrierIds (OwnershipAmbient.retained (.callChannels activation [] :: ambient)) = [])
    (ready : OpenDestinationBacking config.layout middle id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (physical : ready.destination.capability.layout = .varr (.int .u8))
    (current : destinationCurrent middle.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    ∃ after, (finishActivation config.layout activation [.varr (.int .u8)] origin
        (execActivationBody (fuel + 3) config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩) >>= fun carriers =>
        deliverCarriers deliveryFuel config.layout [.construct id] carriers origin) before = .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.returned [.completed id] :: ambient) types live regions
        [⟨[.construct id], [.completed id]⟩] ∧
      after.objects = middle.objects ∧ after.objectOrdinals = middle.objectOrdinals ∧
      after.nextAct = middle.nextAct ∧ after.nextScope = middle.nextScope ∧
      (∀ storageId, ready.destination.backing = .direct storageId →
        Nonempty (BuiltByteReceiver config.layout after id storageId bytes.length)) := by
  apply byteBody_finish_world_separated fuel deliveryFuel config initialized activation scope id bytes origin before boundState middle
    ambient types live regions channels bound normal absent world history ?_ ready packed adaptation receiver request physical current fits mutable cutoff covered
  intro retained member
  rw [noRetained] at member
  cases member

theorem byteBody_finish_world_delivery (fuel deliveryFuel : Nat) (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (scope id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before boundState middle : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (channels : activation.channels = [.construct id])
    (bound : bindAll activation.act before.nextScope [] (ownershipResultScopeState activation scope before) = .ok () boundState)
    (normal : execStmts (fuel + 2) config { activation with scopes := (scope, before.nextScope) :: activation.scopes }
      [] boundState = .ok (.normal .unit) middle)
    (absent : ∀ descriptor ∈ activation.vars.toList, descriptor.scope ≠ scope)
    (world : AcceptedWorld config initialized middle (.callChannels activation [] :: ambient) types live regions [])
    (history : ReservationReferencesBounded middle.construction (.callChannels activation [] :: ambient))
    (noRetained : completedCarrierIds (OwnershipAmbient.retained (.callChannels activation [] :: ambient)) = [])
    (ready : OpenDestinationBacking config.layout middle id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (physical : ready.destination.capability.layout = .varr (.int .u8))
    (current : destinationCurrent middle.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    ∃ after, (finishActivation config.layout activation [.varr (.int .u8)] origin
        (execActivationBody (fuel + 3) config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩) >>= fun carriers =>
        deliverCarriers deliveryFuel config.layout [.construct id] carriers origin) before = .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.returned [.completed id] :: ambient) types live regions
        [⟨[.construct id], [.completed id]⟩] := by
  obtain ⟨after, done, finalWorld, objects, ordinals, acts, scopes, geometry⟩ := byteBody_finish_world_observed fuel deliveryFuel config initialized
    activation scope id bytes origin before boundState middle ambient types live regions channels bound normal absent world history noRetained
    ready packed adaptation receiver request physical current fits mutable cutoff covered
  exact ⟨after, done, finalWorld⟩

theorem byteBody_finish_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (scope id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before boundState middle : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (channels : activation.channels = [.construct id])
    (bound : bindAll activation.act before.nextScope [] (ownershipResultScopeState activation scope before) = .ok () boundState)
    (normal : execStmts (fuel + 2) config { activation with scopes := (scope, before.nextScope) :: activation.scopes }
      [] boundState = .ok (.normal .unit) middle)
    (absent : ∀ descriptor ∈ activation.vars.toList, descriptor.scope ≠ scope)
    (world : AcceptedWorld config initialized middle (.callChannels activation [] :: ambient) types live regions [])
    (history : ReservationReferencesBounded middle.construction (.callChannels activation [] :: ambient))
    (noRetained : completedCarrierIds (OwnershipAmbient.retained (.callChannels activation [] :: ambient)) = [])
    (ready : OpenDestinationBacking config.layout middle id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (physical : ready.destination.capability.layout = .varr (.int .u8))
    (current : destinationCurrent middle.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    ∃ after, (finishActivation config.layout activation [.varr (.int .u8)] origin
        (execActivationBody (fuel + 3) config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩) >>= fun carriers =>
        deliverCarriers fuel config.layout [.construct id] carriers origin) before = .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.returned [.completed id] :: ambient) types live regions
        [⟨[.construct id], [.completed id]⟩] := by
  exact byteBody_finish_world_delivery fuel fuel config initialized activation scope id bytes origin before boundState middle
    ambient types live regions channels bound normal absent world history noRetained ready packed adaptation receiver request
    physical current fits mutable cutoff covered

theorem byteBody_finish_from_activation_separated (fuel deliveryFuel : Nat) (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (scope id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (channels : activation.channels = [.construct id])
    (absent : ∀ descriptor ∈ activation.vars.toList, descriptor.scope ≠ scope)
    (world : AcceptedWorld config initialized before (.callChannels activation [] :: ambient) types live regions [])
    (history : ReservationReferencesBounded before.construction (.callChannels activation [] :: ambient))
    (separated : ∀ retained ∈ completedCarrierIds (OwnershipAmbient.retained (.callChannels activation [] :: ambient)),
      destinationDescendant before.construction.destinations id retained = false)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (physical : ready.destination.capability.layout = .varr (.int .u8))
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    ∃ after, (finishActivation config.layout activation [.varr (.int .u8)] origin
        (execActivationBody (fuel + 3) config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩) >>= fun carriers =>
        deliverCarriers deliveryFuel config.layout [.construct id] carriers origin) before = .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.returned [.completed id] :: ambient) types live regions
        [⟨[.construct id], [.completed id]⟩] ∧
      after.objects = before.objects ∧ after.objectOrdinals = before.objectOrdinals ∧
      after.nextAct = before.nextAct ∧ after.nextScope = before.nextScope + 1 ∧
      (∀ storageId, ready.destination.backing = .direct storageId →
        Nonempty (BuiltByteReceiver config.layout after id storageId bytes.length)) := by
  let scopeState := ownershipResultScopeState activation scope before
  have scopedWorld := acceptedWorld_resultScope config initialized before (.callChannels activation [] :: ambient)
    types live regions [] activation scope world
  have bound : bindAll activation.act before.nextScope [] scopeState = .ok () scopeState := by simp [bindAll, bind, pure]
  have normal : execStmts (fuel + 2) config { activation with scopes := (scope, before.nextScope) :: activation.scopes }
      [] scopeState = .ok (.normal .unit) scopeState := by simp [execStmts, pure]
  let scopeReady : OpenDestinationBacking config.layout scopeState id (.varr (.int .u8)) 0 :=
    { ready with present := ready.present, bytes := ready.bytes }
  obtain ⟨after, done, finalWorld, objects, ordinals, acts, scopes, geometry⟩ := byteBody_finish_world_separated fuel deliveryFuel config initialized
    activation scope id bytes origin before scopeState scopeState ambient types live regions channels bound normal absent scopedWorld
    history separated scopeReady packed adaptation receiver request physical current fits mutable cutoff covered
  exact ⟨after, done, finalWorld, objects, ordinals, acts, scopes, geometry⟩

theorem byteBody_finish_from_activation_observed (fuel deliveryFuel : Nat) (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (scope id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (channels : activation.channels = [.construct id])
    (absent : ∀ descriptor ∈ activation.vars.toList, descriptor.scope ≠ scope)
    (world : AcceptedWorld config initialized before (.callChannels activation [] :: ambient) types live regions [])
    (history : ReservationReferencesBounded before.construction (.callChannels activation [] :: ambient))
    (noRetained : completedCarrierIds (OwnershipAmbient.retained (.callChannels activation [] :: ambient)) = [])
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (physical : ready.destination.capability.layout = .varr (.int .u8))
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    ∃ after, (finishActivation config.layout activation [.varr (.int .u8)] origin
        (execActivationBody (fuel + 3) config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩) >>= fun carriers =>
        deliverCarriers deliveryFuel config.layout [.construct id] carriers origin) before = .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.returned [.completed id] :: ambient) types live regions
        [⟨[.construct id], [.completed id]⟩] ∧
      after.objects = before.objects ∧ after.objectOrdinals = before.objectOrdinals ∧
      after.nextAct = before.nextAct ∧ after.nextScope = before.nextScope + 1 ∧
      (∀ storageId, ready.destination.backing = .direct storageId →
        Nonempty (BuiltByteReceiver config.layout after id storageId bytes.length)) := by
  apply byteBody_finish_from_activation_separated fuel deliveryFuel config initialized activation scope id bytes origin before ambient types live regions
    channels absent world history ?_ ready packed adaptation receiver request physical current fits mutable cutoff covered
  intro retained member
  rw [noRetained] at member
  cases member

theorem byteBody_finish_from_activation_delivery (fuel deliveryFuel : Nat) (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (scope id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (channels : activation.channels = [.construct id])
    (absent : ∀ descriptor ∈ activation.vars.toList, descriptor.scope ≠ scope)
    (world : AcceptedWorld config initialized before (.callChannels activation [] :: ambient) types live regions [])
    (history : ReservationReferencesBounded before.construction (.callChannels activation [] :: ambient))
    (noRetained : completedCarrierIds (OwnershipAmbient.retained (.callChannels activation [] :: ambient)) = [])
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (physical : ready.destination.capability.layout = .varr (.int .u8))
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    ∃ after, (finishActivation config.layout activation [.varr (.int .u8)] origin
        (execActivationBody (fuel + 3) config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩) >>= fun carriers =>
        deliverCarriers deliveryFuel config.layout [.construct id] carriers origin) before = .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.returned [.completed id] :: ambient) types live regions
        [⟨[.construct id], [.completed id]⟩] := by
  obtain ⟨after, done, finalWorld, objects, ordinals, acts, scopes, geometry⟩ := byteBody_finish_from_activation_observed fuel deliveryFuel config initialized
    activation scope id bytes origin before ambient types live regions channels absent world history noRetained ready packed adaptation
    receiver request physical current fits mutable cutoff covered
  exact ⟨after, done, finalWorld⟩

theorem byteBody_finish_from_activation (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (scope id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (channels : activation.channels = [.construct id])
    (absent : ∀ descriptor ∈ activation.vars.toList, descriptor.scope ≠ scope)
    (world : AcceptedWorld config initialized before (.callChannels activation [] :: ambient) types live regions [])
    (history : ReservationReferencesBounded before.construction (.callChannels activation [] :: ambient))
    (noRetained : completedCarrierIds (OwnershipAmbient.retained (.callChannels activation [] :: ambient)) = [])
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (physical : ready.destination.capability.layout = .varr (.int .u8))
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    ∃ after, (finishActivation config.layout activation [.varr (.int .u8)] origin
        (execActivationBody (fuel + 3) config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩) >>= fun carriers =>
        deliverCarriers fuel config.layout [.construct id] carriers origin) before = .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.returned [.completed id] :: ambient) types live regions
        [⟨[.construct id], [.completed id]⟩] := by
  exact byteBody_finish_from_activation_delivery fuel fuel config initialized activation scope id bytes origin before ambient
    types live regions channels absent world history noRetained ready packed adaptation receiver request physical current fits
    mutable cutoff covered

#print axioms byteBody_finish_world_separated
#print axioms byteBody_finish_from_activation_separated
#print axioms byteBody_finish_from_activation_observed
#print axioms byteBody_finish_world_observed
#print axioms byteBody_finish_from_activation_delivery
#print axioms byteBody_finish_world_delivery
#print axioms byteBody_finish_from_activation
#print axioms byteBody_finish_world
end Goose.Proofs.ConstructionAcceptedExecution

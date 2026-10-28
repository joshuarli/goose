import Goose.Proofs.ConstructionByteLocalStopped

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem constructLocal_byteOwner_success_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId)
    (before after : ExecutionState) (carrier : Carrier) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (executed : constructLocal ⟨config.module, environment.vars⟩ environment.act (.varr (.int .u8)) origin
      (.bytes (.varr (.int .u8)) bytes bytesOrigin)
      (fun destination => buildExpr (fuel + 1) config environment destination (.bytes (.varr (.int .u8)) bytes bytesOrigin)) before =
      .ok carrier after) :
    AcceptedWorld config initialized after ambient types live regions pending ∧
      Nonempty (FreshDestinationFrame before after) ∧
      ∃ stored, carrier = .completed before.construction.destinations.size ∧
        storedDestination before.construction.destinations.size after = .ok stored after ∧
        StoredValueBacking config.layout after stored ∧ stored.storage = before.construction.storage.size ∧
        stored.destination = some before.construction.destinations.size ∧ stored.ty = .varr (.int .u8) := by
  simp only [constructLocal, producerCount?, literalCount, bind] at executed
  cases created : newDestination config.layout environment.act (.varr (.int .u8)) .value origin none (some bytes.length) before with
  | stop reason state | escape reason carriers state | jump reason kind state =>
    simp only [EvalConfig.layout] at created
    simp only [created] at executed
    cases executed
  | ok id allocated =>
    have created' := created
    simp only [EvalConfig.layout] at created'
    simp only [created'] at executed
    cases constructed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes bytesOrigin) allocated with
    | stop reason state | escape reason carriers state | jump reason kind state => simp only [constructed] at executed; cases executed
    | ok result built =>
      cases result
      simp only [constructed] at executed
      cases completed : completedReceivingDestination id built with
      | stop reason state | escape reason carriers state | jump reason kind state => simp only [completed] at executed; cases executed
      | ok selected checked =>
        simp only [completed] at executed
        have freshId := newDestination_fresh_id config.layout environment.act (.varr (.int .u8)) .value origin
          (some bytes.length) before allocated id created
        subst id
        obtain ⟨frame⟩ := newDestination_fresh_frame config.layout environment.act (.varr (.int .u8)) .value origin
          (some bytes.length) before allocated before.construction.destinations.size world.ownership.source.structural.1.1.1 created
        obtain ⟨ready⟩ := newDestination_initial_backing config.layout environment.act (.varr (.int .u8)) .value origin
          (some bytes.length) before allocated before.construction.destinations.size (.int .u8) rfl created
        obtain ⟨row, present, packed, request, direct, receiver⟩ := newDestination_byteOwner_packed_value config.layout
          environment.act origin (some bytes.length) before allocated before.construction.destinations.size created
        have framePresent : allocated.construction.destinations[before.construction.destinations.size]? = some frame.row := by
          rw [frame.destinations]; exact Array.getElem?_push_size
        have same : row = frame.row := Option.some.inj (present.symm.trans framePresent)
        subst row
        have allocatedWorld := newDestination_acceptedWorld config environment.act (.varr (.int .u8)) .value origin
          (some bytes.length) initialized before allocated before.construction.destinations.size ambient types live regions pending world created
        have current := newDestination_current_self config initialized environment.act (.varr (.int .u8)) .value origin
          (some bytes.length) before allocated before.construction.destinations.size ambient types live regions pending world created
        obtain ⟨builtFrame, _⟩ := buildExpr_byteOwner_freshFrame fuel config environment bytes bytesOrigin before allocated built
          frame before.construction.storage.size 0 ready direct rfl packed request allocatedWorld.ownership.source.structural.1.1.1 current constructed
        have currentBuilt := frame.same_current builtFrame before.construction.destinations.size current
        obtain ⟨sameId, sameState⟩ := completedReceivingDestination_self before.construction.destinations.size built checked selected currentBuilt completed
        subst selected checked
        cases published : publishCarriers origin [.completed before.construction.destinations.size] built with
        | stop reason state | escape reason carriers state | jump reason kind state => simp only [published] at executed; cases executed
        | ok result final =>
          cases result
          simp only [published, pure, ExecutionStep.ok.injEq] at executed
          obtain ⟨sameCarrier, sameState⟩ := executed
          subst carrier after
          obtain ⟨finalWorld, finalFrame, stored, sampled, backed, storage, named, valueType⟩ :=
            allocated_published_byteOwner_world fuel config initialized environment bytes origin bytesOrigin before allocated built final
              before.construction.destinations.size ambient types live regions pending world created constructed published
          exact ⟨finalWorld, finalFrame, stored, rfl, sampled, backed, storage, named, valueType⟩

#print axioms constructLocal_byteOwner_success_world
end Goose.Proofs.ConstructionAcceptedExecution

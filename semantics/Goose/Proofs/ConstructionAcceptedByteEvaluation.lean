import Goose.Proofs.ConstructionAcceptedByteFrame

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem evalValue_byteOwner_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (before after : ExecutionState) (value : Value) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (executed : evalValue (fuel + 2) config environment (.bytes (.varr (.int .u8)) bytes origin) before = .ok value after) :
    AcceptedWorld config initialized after ambient types live regions pending ∧
      ∃ stored, value = .stored stored ∧ StoredValueBacking config.layout after stored ∧
        stored.storage = before.construction.storage.size ∧
        stored.destination = some before.construction.destinations.size := by
  simp only [evalValue, Ty.nonfixed, constructLocal, producerCount?, literalCount, bind, ↓reduceIte] at executed
  cases created : newDestination (LayoutEnv.ofModule config.module) environment.act (.varr (.int .u8)) .value origin none
      (some bytes.length) before with
  | stop reason state | escape reason carriers state | jump reason kind state =>
    simp only [created] at executed
    cases executed
  | ok id allocated =>
    simp only [created] at executed
    cases constructed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) allocated with
    | stop reason state | escape reason carriers state | jump reason kind state =>
      simp only [constructed] at executed
      cases executed
    | ok result built =>
      cases result
      simp only [constructed] at executed
      cases completed : completedReceivingDestination id built with
      | stop reason state | escape reason carriers state | jump reason kind state =>
        simp only [completed] at executed
        cases executed
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
        obtain ⟨builtFrame, _⟩ := buildExpr_byteOwner_freshFrame fuel config environment bytes origin before allocated built
          frame before.construction.storage.size 0 ready direct rfl packed request allocatedWorld.ownership.source.structural.1.1.1 current constructed
        have sizes : built.construction.destinations.size = allocated.construction.destinations.size := by
          rw [builtFrame.destinations, frame.destinations]
          simp only [Array.size_push]
        have successors : built.construction.destinationSuccessors = allocated.construction.destinationSuccessors :=
          builtFrame.successors.trans frame.successors.symm
        have currentBuilt : destinationCurrent built.construction before.construction.destinations.size =
            .ok before.construction.destinations.size := by
          rw [destinationCurrent_result, destinationCurrentSteps_same_indexing _ allocated.construction built.construction sizes successors, sizes]
          simpa only [destinationCurrent_result] using current
        simp only [completedReceivingDestination, receivingDestination, liftConstruction, currentBuilt, bind,
          completedDestination, getDestination, EvalM.get] at completed
        cases found : built.construction.destinations[before.construction.destinations.size]? with
        | none => simp only [found, fault, EvalM.stop] at completed; cases completed
        | some destination =>
          simp only [found, pure] at completed
          cases progress : destination.progress <;>
            simp_all only [pure, fault, EvalM.stop, ExecutionStep.ok.injEq, reduceCtorEq]
          all_goals try contradiction
          all_goals
            obtain ⟨sameId, sameState⟩ := completed
            subst checked
            subst selected
            cases published : publishCarriers origin [.completed before.construction.destinations.size] built with
            | stop reason state | escape reason carriers state | jump reason kind state =>
              simp only [published] at executed
              cases executed
            | ok result final =>
              cases result
              simp only [published, pure, carrierValue, bind] at executed
              obtain ⟨finalWorld, stored, sampled, backed, storage, named⟩ :=
                allocated_published_byteOwner_world fuel config initialized environment bytes origin before allocated built final
                  before.construction.destinations.size ambient types live regions pending world created constructed published
              simp only [sampled, ExecutionStep.ok.injEq] at executed
              obtain ⟨sameValue, sameState⟩ := executed
              subst after
              subst value
              exact ⟨finalWorld, stored, rfl, backed, storage, named⟩

#print axioms evalValue_byteOwner_world

end Goose.Proofs.ConstructionAcceptedExecution

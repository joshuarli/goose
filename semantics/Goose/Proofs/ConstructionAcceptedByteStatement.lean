import Goose.Proofs.ConstructionAcceptedByteBinding

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem completedReceivingDestination_self (id : Nat) (before after : ExecutionState) (selected : Nat)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : completedReceivingDestination id before = .ok selected after) : selected = id ∧ after = before := by
  simp only [completedReceivingDestination, receivingDestination, liftConstruction, current, bind,
    completedDestination, getDestination, EvalM.get] at executed
  cases found : before.construction.destinations[id]? with
  | none => simp only [found, fault, EvalM.stop] at executed; cases executed
  | some row =>
    simp only [found, pure] at executed
    cases progress : row.progress <;> simp_all only [fault, EvalM.stop, ExecutionStep.ok.injEq, reduceCtorEq]
    all_goals exact ⟨trivial, executed.2.symm⟩

theorem FreshDestinationFrame.same_current {before first second : ExecutionState}
    (firstFrame : FreshDestinationFrame before first) (secondFrame : FreshDestinationFrame before second)
    (id : Nat) (current : destinationCurrent first.construction id = .ok id) :
    destinationCurrent second.construction id = .ok id := by
  have sizes : second.construction.destinations.size = first.construction.destinations.size := by
    rw [secondFrame.destinations, firstFrame.destinations]
    simp only [Array.size_push]
  have successors : second.construction.destinationSuccessors = first.construction.destinationSuccessors :=
    secondFrame.successors.trans firstFrame.successors.symm
  rw [destinationCurrent_result, destinationCurrentSteps_same_indexing _ first.construction second.construction sizes successors, sizes]
  simpa only [destinationCurrent_result] using current

theorem storedDestination_object_none (id : Nat) (state : ExecutionState) (stored : StoredValue)
    (sampled : storedDestination id state = .ok stored state) : stored.object = none := by
  simp only [storedDestination, getDestination, EvalM.get, bind] at sampled
  cases found : state.construction.destinations[id]? with
  | none => simp only [found, fault, EvalM.stop] at sampled; cases sampled
  | some row =>
    simp only [found, pure] at sampled
    cases progress : progressCount row.progress with
    | none => simp only [progress, fault, EvalM.stop] at sampled; cases sampled
    | some count =>
      simp only [progress, ExecutionStep.ok.injEq] at sampled
      obtain ⟨rfl, _⟩ := sampled
      rfl

theorem execStmt_byteOwner_letWorld (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (localVar : Nat) (descriptor : LocalVar) (implementation : Impl)
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) (before after : ExecutionState) (root : Goose.Core.RootInst)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (declared : environment.vars[localVar]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (unnamed : (implementation.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some localVar)) = none)
    (resolved : rootOf environment localVar before = .ok root before)
    (compatible : RootTypeCompatible types root (.varr (.int .u8)))
    (conforms : LayoutConforms config.layout (.varr (.int .u8)))
    (fresh : before.objectOrdinals.lookup root = none)
    (freshType : ∀ act scope id, root = .local act scope id → act < before.nextAct ∧ scope < before.nextScope)
    (freshSynthetic : ∀ id, root = .global id → config.module.globals.size ≤ id →
      id < config.module.globals.size + before.nextScope)
    (executed : execStmt (fuel + 2) config environment (.letS localVar (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before =
      .ok (.normal .unit) after) :
    ∃ (stored : StoredValue) (published : ExecutionState),
      Nonempty (FreshDestinationFrame before published) ∧
      storedDestination before.construction.destinations.size published = .ok stored published ∧
      bindRoot root (.stored stored) published = .ok () after ∧
      RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
      AcceptedWorld config initialized after ambient (registerRootType types root (.varr (.int .u8)))
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending := by
  simp only [execStmt, declared, ty, Ty.nonfixed, implementationFound, unnamed, ordinaryProducerCount?,
    producerCount?, literalCount, Option.isSome_some, ↓reduceIte, materializeProducer, bind, pure, resolved,
    Option.isNone_none, Option.isSome_none, Option.map_none] at executed
  simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_eq_orElse, Option.orElse] at executed
  cases created : newDestination config.layout environment.act (.varr (.int .u8)) .value origin none
      (some bytes.length) before with
  | stop reason state | escape reason carriers state | jump reason kind state =>
    simp only [created] at executed
    cases executed
  | ok id allocated =>
    simp only [created] at executed
    cases constructed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes bytesOrigin) allocated with
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
        obtain ⟨builtFrame, _⟩ := buildExpr_byteOwner_freshFrame fuel config environment bytes bytesOrigin before allocated built
          frame before.construction.storage.size 0 ready direct rfl packed request allocatedWorld.ownership.source.structural.1.1.1 current constructed
        have currentBuilt := frame.same_current builtFrame before.construction.destinations.size current
        obtain ⟨sameId, sameState⟩ := completedReceivingDestination_self before.construction.destinations.size built checked selected currentBuilt completed
        subst selected checked
        cases published : publishCarriers origin [.completed before.construction.destinations.size] built with
        | stop reason state | escape reason carriers state | jump reason kind state =>
          simp only [published] at executed
          cases executed
        | ok result final =>
          cases result
          simp only [published] at executed
          obtain ⟨stored, boundState, sampled, bound, extended, finalWorld⟩ :=
            allocated_published_byteOwner_bindWorld fuel config initialized environment bytes origin bytesOrigin before allocated built final
              before.construction.destinations.size root ambient types live regions pending world compatible conforms fresh freshType
              freshSynthetic created constructed published
          simp only [sampled] at executed
          obtain ⟨_, publishedFrame, value, sampled', backed, identity, named, valueType⟩ :=
            allocated_published_byteOwner_world fuel config initialized environment bytes origin bytesOrigin before allocated built final
              before.construction.destinations.size ambient types live regions pending world created constructed published
          have sameValue : stored = value := (ExecutionStep.ok.inj (sampled.symm.trans sampled')).1
          subst value
          have objectNone := storedDestination_object_none before.construction.destinations.size final stored sampled
          have sameStored : { stored with ty := .varr (.int .u8), object := none } = stored := by
            cases stored
            simp_all
          rw [sameStored, bound] at executed
          cases executed
          exact ⟨stored, final, publishedFrame, sampled, bound, extended, finalWorld⟩

#print axioms completedReceivingDestination_self
#print axioms FreshDestinationFrame.same_current
#print axioms storedDestination_object_none
#print axioms execStmt_byteOwner_letWorld

end Goose.Proofs.ConstructionAcceptedExecution

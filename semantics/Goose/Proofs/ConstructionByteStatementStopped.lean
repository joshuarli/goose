import Goose.Proofs.ConstructionByteValueComplete

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem execStmt_byteOwner_stopped_afterAllocation (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (sourceFrame : ConstructionSourceFrame) (before allocated after : ExecutionState)
    (id : Nat) (descriptor : LocalVar) (implementation : Impl) (root : Goose.Core.RootInst)
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) (destination : Nat) (stop : Goose.Core.Stop)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config sourceFrame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted sourceFrame before types)
    (declared : sourceFrame.interpretation.environment.vars[id]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (implementationFound : config.module.impls[sourceFrame.interpretation.environment.implementation]? = some implementation)
    (unnamed : (implementation.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none)
    (resolved : rootOf sourceFrame.interpretation.environment id before = .ok root before)
    (created : newDestination config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin none
      (some bytes.length) before = .ok destination allocated)
    (executed : execStmt (fuel + 2) config sourceFrame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .stop stop after) :
    AcceptedWorld config sourceFrame.initialized after ambient types live (freshReceivingRegion before destination :: regions) pending ∧
      AcceptedFrame config accepted sourceFrame after types := by
  simp only [execStmt, declared, ty, Ty.nonfixed, implementationFound, unnamed, ordinaryProducerCount?,
    producerCount?, literalCount, Option.isSome_some, ↓reduceIte, materializeProducer, bind, pure, resolved,
    Option.isNone_none, Option.isSome_none, Option.map_none] at executed
  simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_eq_orElse, Option.orElse, created] at executed
  cases constructed : buildExpr (fuel + 1) config sourceFrame.interpretation.environment destination
      (.bytes (.varr (.int .u8)) bytes bytesOrigin) allocated with
  | stop reason state =>
    simp only [constructed, ExecutionStep.stop.injEq] at executed
    obtain ⟨rfl, rfl⟩ := executed
    exact buildExpr_byteOwner_stopped_world fuel config accepted sourceFrame before allocated state bytes origin bytesOrigin destination reason
      ambient types live regions pending world source created constructed
  | escape address carriers state =>
    have localAction := buildExpr_byteOwner_local fuel config sourceFrame.interpretation.environment destination (.varr (.int .u8)) bytes bytesOrigin allocated
    rw [constructed] at localAction
    cases localAction
  | jump target kind state =>
    have localAction := buildExpr_byteOwner_local fuel config sourceFrame.interpretation.environment destination (.varr (.int .u8)) bytes bytesOrigin allocated
    rw [constructed] at localAction
    cases localAction
  | ok result built =>
    cases result
    simp only [constructed] at executed
    have freshId := newDestination_fresh_id config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
      (some bytes.length) before allocated destination created
    subst destination
    let id := before.construction.destinations.size
    change buildExpr (fuel + 1) config sourceFrame.interpretation.environment id
      (.bytes (.varr (.int .u8)) bytes bytesOrigin) allocated = .ok () built at constructed
    obtain ⟨frame⟩ := newDestination_fresh_frame config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
      (some bytes.length) before allocated id world.ownership.source.structural.1.1.1 created
    obtain ⟨ready⟩ := newDestination_initial_backing config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
      (some bytes.length) before allocated id (.int .u8) rfl created
    obtain ⟨row, present, packed, request, direct, receiver⟩ := newDestination_byteOwner_packed_value config.layout
      sourceFrame.interpretation.environment.act origin (some bytes.length) before allocated id created
    have framePresent : allocated.construction.destinations[id]? = some frame.row := by
      rw [frame.destinations]; exact Array.getElem?_push_size
    have same : row = frame.row := Option.some.inj (present.symm.trans framePresent)
    subst row
    have allocatedWorld := newDestination_acceptedWorld config sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
      (some bytes.length) sourceFrame.initialized before allocated id ambient types live regions pending world created
    have current := newDestination_current_self config sourceFrame.initialized sourceFrame.interpretation.environment.act (.varr (.int .u8))
      .value origin (some bytes.length) before allocated id ambient types live regions pending world created
    obtain ⟨builtFrame, _⟩ := buildExpr_byteOwner_freshFrame fuel config sourceFrame.interpretation.environment bytes bytesOrigin before allocated built
      frame before.construction.storage.size 0 ready direct rfl packed request allocatedWorld.ownership.source.structural.1.1.1 current constructed
    have currentBuilt := frame.same_current builtFrame id current
    have fits := newDestination_byteOwner_count_bound config.layout sourceFrame.interpretation.environment.act origin bytes.length before allocated id created
    have readySame : ready.destination = frame.row := Option.some.inj (ready.present.symm.trans framePresent)
    obtain ⟨builtRow, storage, builtPresent, stored, _, _, _, _, _, builtProgress, _⟩ :=
      buildExpr_byteOwner_geometry fuel config sourceFrame.interpretation.environment bytes bytesOrigin id 0 allocated built ready
        (by rw [readySame]; exact packed) (by rw [readySame]; exact request) (by simpa using fits)
        allocatedWorld.ownership.source.structural.1.1.1 current constructed
    have completed : completedReceivingDestination id built = .ok id built := by
      simp only [completedReceivingDestination, receivingDestination, liftConstruction, currentBuilt, bind,
        completedDestination, getDestination, EvalM.get, builtPresent, builtProgress, pure]
    have completed' := completed
    dsimp only [id] at completed'
    simp only [completed'] at executed
    cases published : publishCarriers origin [.completed id] built with
    | stop reason state =>
      have published' := published
      dsimp only [id] at published'
      simp only [published', ExecutionStep.stop.injEq] at executed
      obtain ⟨rfl, rfl⟩ := executed
      exact allocated_byteOwner_publishStop_world fuel config accepted sourceFrame before allocated built state bytes origin bytesOrigin id reason
        ambient types live regions pending world source created constructed published
    | escape address carriers state =>
      have localAction := publishCompleted_local origin id built
      rw [published] at localAction
      cases localAction
    | jump target kind state =>
      have localAction := publishCompleted_local origin id built
      rw [published] at localAction
      cases localAction
    | ok value final =>
      cases value
      have published' := published
      dsimp only [id] at published'
      simp only [published'] at executed
      obtain ⟨_, _, stored, sampled, _, _, _, _⟩ := allocated_published_byteOwner_world fuel config sourceFrame.initialized
        sourceFrame.interpretation.environment bytes origin bytesOrigin before allocated built final id ambient types live regions pending
        world created constructed published
      dsimp only [id] at sampled
      simp only [sampled] at executed
      have bound : ∃ result, bindRoot root (.stored { stored with ty := .varr (.int .u8), object := none }) final = .ok () result := by
        simp only [bindRoot, EvalM.get, bind]
        split <;> simp [setObjectOrdinal, bindStaticRoot, EvalM.get, EvalM.set, bind]
      obtain ⟨result, bound⟩ := bound
      simp only [bound, reduceCtorEq] at executed

theorem execStmt_byteOwner_stopped_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (sourceFrame : ConstructionSourceFrame) (before after : ExecutionState)
    (id : Nat) (descriptor : LocalVar) (implementation : Impl) (root : Goose.Core.RootInst)
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) (stop : Goose.Core.Stop)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config sourceFrame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted sourceFrame before types)
    (declared : sourceFrame.interpretation.environment.vars[id]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (implementationFound : config.module.impls[sourceFrame.interpretation.environment.implementation]? = some implementation)
    (unnamed : (implementation.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none)
    (resolved : rootOf sourceFrame.interpretation.environment id before = .ok root before)
    (executed : execStmt fuel config sourceFrame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .stop stop after) :
    ∃ nextRegions, AcceptedWorld config sourceFrame.initialized after ambient types live nextRegions pending ∧
      AcceptedFrame config accepted sourceFrame after types := by
  cases fuel with
  | zero =>
    simp only [execStmt, timeout, EvalM.stop, ExecutionStep.stop.injEq] at executed
    obtain ⟨_, same⟩ := executed
    subst after
    exact ⟨regions, world, source⟩
  | succ fuel =>
    cases created : newDestination config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin none
        (some bytes.length) before with
    | stop reason final =>
      simp only [execStmt, declared, ty, Ty.nonfixed, implementationFound, unnamed, ordinaryProducerCount?,
        producerCount?, literalCount, Option.isSome_some, ↓reduceIte, materializeProducer, bind, pure, resolved,
        Option.isNone_none, Option.isSome_none, Option.map_none, Bool.false_eq_true, Option.orElse_eq_orElse,
        Option.orElse, created, ExecutionStep.stop.injEq] at executed
      obtain ⟨rfl, rfl⟩ := executed
      exact ⟨regions, newDestination_byteOwner_stopped_world config sourceFrame.initialized
        sourceFrame.interpretation.environment.act origin bytes.length before final reason ambient types live regions pending world created,
        newDestination_byteOwner_stopped_frame sourceFrame.interpretation.environment.act origin bytes.length reason source created⟩
    | escape address carriers final =>
      have localAction := newByteDestination_local config sourceFrame.interpretation.environment origin bytes.length before
      rw [created] at localAction
      cases localAction
    | jump target kind final =>
      have localAction := newByteDestination_local config sourceFrame.interpretation.environment origin bytes.length before
      rw [created] at localAction
      cases localAction
    | ok destination allocated =>
      cases fuel with
      | zero =>
        simp only [execStmt, declared, ty, Ty.nonfixed, implementationFound, unnamed, ordinaryProducerCount?,
          producerCount?, literalCount, Option.isSome_some, ↓reduceIte, materializeProducer, bind, pure, resolved,
          Option.isNone_none, Option.isSome_none, Option.map_none, Bool.false_eq_true, Option.orElse_eq_orElse,
          Option.orElse, created, buildExpr, timeout, EvalM.stop, ExecutionStep.stop.injEq] at executed
        obtain ⟨rfl, rfl⟩ := executed
        have finalWorld := newDestination_acceptedWorld config sourceFrame.interpretation.environment.act (.varr (.int .u8))
          .value origin (some bytes.length) sourceFrame.initialized before allocated destination ambient types live regions pending world created
        obtain ⟨frame⟩ := newDestination_fresh_frame config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8))
          .value origin (some bytes.length) before allocated destination world.ownership.source.structural.1.1.1 created
        exact ⟨freshReceivingRegion before destination :: regions, finalWorld, frame.acceptedFrame source⟩
      | succ fuel =>
        exact ⟨freshReceivingRegion before destination :: regions,
          execStmt_byteOwner_stopped_afterAllocation fuel config accepted sourceFrame before allocated after id descriptor implementation root
            bytes origin bytesOrigin destination stop ambient types live regions pending world source declared ty implementationFound unnamed
            resolved created executed⟩

theorem execStmt_acceptedByteOwner_stopped_world (fuel : Nat) (typeFuel : Nat) (config : EvalConfig)
    (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (context id scope scopeInst : Nat)
    (outer : List (Nat × Nat)) (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId)
    (before after : ExecutionState) (stop : Goose.Core.Stop) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (typingNext : TypingEnv) (typingAfter : Nat)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (typed : typeStatement (typeFuel + 1) frame.typing (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)
      frame.typingCounter = .ok (typingNext, typingAfter))
    (byteOwner : (frame.typing.variables[id]?).map (·.ty) = some (.varr (.int .u8)))
    (scopes : frame.interpretation.environment.scopes = (scope, scopeInst) :: outer)
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none)
    (executed : execStmt fuel config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .stop stop after) :
    ∃ nextRegions, AcceptedWorld config frame.initialized after ambient types live nextRegions pending ∧
      AcceptedFrame config accepted frame after types := by
  obtain ⟨descriptor, declared, localScope, typingOrder⟩ := typeStatement_let_descriptor typeFuel frame.typing typingNext id
    (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin frame.typingCounter typingAfter typed
  have descriptorType : descriptor.ty = .varr (.int .u8) := by
    simpa only [declared, Option.map_some, Option.some.injEq] using byteOwner
  have sourceScopes : frame.source.scopes = scope :: outer.map Prod.fst := by
    rw [source.compatible.scopes, scopes]
    rfl
  have localScope' := localScope.trans (source.compatible.currentScope scope (outer.map Prod.fst) sourceScopes)
  have runtimeDeclared : frame.interpretation.environment.vars[id]? = some descriptor := by
    rw [source.compatible.variables]
    exact declared
  let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
  have resolved : rootOf frame.interpretation.environment id before = .ok root before := by
    simp only [rootOf, runtimeDeclared, scopes, List.find?_cons, localScope', beq_self_eq_true, pure, root]
  have originFact := source.compatible.origin
  unfold SourceOrigin at originFact
  rw [phase] at originFact
  obtain ⟨original, calls, contextFound, implementationFound, implementationId, rest⟩ := originFact
  have implementation : config.module.impls[frame.interpretation.environment.implementation]? = some frame.source.impl := by
    rw [implementationId]
    exact implementationFound
  exact execStmt_byteOwner_stopped_world fuel config accepted frame before after id descriptor frame.source.impl root bytes origin bytesOrigin
    stop ambient types live regions pending world source runtimeDeclared descriptorType implementation unnamed resolved executed

#print axioms execStmt_acceptedByteOwner_stopped_world
#print axioms execStmt_byteOwner_stopped_world
#print axioms execStmt_byteOwner_stopped_afterAllocation
end Goose.Proofs.ConstructionAcceptedExecution

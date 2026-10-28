import Goose.Proofs.ConstructionAcceptedByteChecked
import Goose.Proofs.ConstructionAcceptedByteContinuation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem liftConstruction_ne_timeout (origin : Goose.Core.OriginId) (action : ConstructionM α)
    (before after : ExecutionState) : liftConstruction origin action before ≠ .stop .timeout after := by
  unfold liftConstruction
  cases action before.construction with
  | ok value state => simp
  | fault kind state => cases kind <;> simp

theorem newDestination_byteOwner_ne_timeout (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (origin : Goose.Core.OriginId) (count : Nat) (before after : ExecutionState) :
    newDestination layout owner (.varr (.int .u8)) .value origin none (some count) before ≠ .stop .timeout after := by
  intro timeout
  simp only [newDestination, bind, receivingLayout, pure] at timeout
  cases reserved : liftConstruction origin reserveStorage before with
  | stop reason state =>
    simp only [reserved] at timeout
    cases timeout
    exact liftConstruction_ne_timeout origin reserveStorage before after reserved
  | escape target carriers state => simp only [reserved] at timeout; cases timeout
  | jump target kind state => simp only [reserved] at timeout; cases timeout
  | ok id state =>
    simp only [reserved] at timeout
    exact liftConstruction_ne_timeout origin _ state after timeout

theorem evalValue_byteOwner_timeout_world (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before after : ExecutionState)
    (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (executed : evalValue 1 config frame.interpretation.environment (.bytes (.varr (.int .u8)) bytes origin) before =
      .stop .timeout after) :
    ∃ id, AcceptedWorld config frame.initialized after ambient types live
      (freshReceivingRegion before id :: regions) pending ∧ AcceptedFrame config accepted frame after types := by
  simp only [evalValue, Ty.nonfixed, constructLocal, producerCount?, literalCount, bind, ↓reduceIte] at executed
  cases created : newDestination (LayoutEnv.ofModule config.module) frame.interpretation.environment.act (.varr (.int .u8)) .value origin none
      (some bytes.length) before with
  | stop reason allocated =>
    simp only [created] at executed
    cases executed
    exact (newDestination_byteOwner_ne_timeout config.layout frame.interpretation.environment.act origin bytes.length before after created).elim
  | escape target carriers allocated | jump target kind allocated => simp only [created] at executed; cases executed
  | ok id allocated =>
    simp only [created, buildExpr, timeout, EvalM.stop] at executed
    cases executed
    have fresh := newDestination_acceptedWorld config frame.interpretation.environment.act (.varr (.int .u8)) .value origin
      (some bytes.length) frame.initialized before after id ambient types live regions pending world created
    obtain ⟨destination⟩ := newDestination_fresh_frame config.layout frame.interpretation.environment.act (.varr (.int .u8)) .value origin
      (some bytes.length) before after id world.ownership.source.structural.1.1.1 created
    exact ⟨id, fresh, destination.acceptedFrame source⟩

theorem execStmt_byteOwner_timeout_world (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (id : Nat) (descriptor : LocalVar) (implementation : Impl)
    (before after : ExecutionState) (root : Goose.Core.RootInst) (bytes : List UInt8)
    (origin bytesOrigin : Goose.Core.OriginId)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (declared : frame.interpretation.environment.vars[id]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (implementationFound : config.module.impls[frame.interpretation.environment.implementation]? = some implementation)
    (unnamed : (implementation.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none)
    (resolved : rootOf frame.interpretation.environment id before = .ok root before)
    (executed : execStmt 1 config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .stop .timeout after) :
    ∃ destination, AcceptedWorld config frame.initialized after ambient types live
      (freshReceivingRegion before destination :: regions) pending ∧ AcceptedFrame config accepted frame after types := by
  simp only [execStmt, declared, ty, Ty.nonfixed, implementationFound, unnamed, ordinaryProducerCount?,
    producerCount?, literalCount, Option.isSome_some, ↓reduceIte, materializeProducer, bind, pure, resolved,
    Option.isNone_none, Option.isSome_none, Option.map_none] at executed
  simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_eq_orElse, Option.orElse] at executed
  cases created : newDestination config.layout frame.interpretation.environment.act (.varr (.int .u8)) .value origin none
      (some bytes.length) before with
  | stop reason allocated =>
    simp only [created] at executed
    cases executed
    exact (newDestination_byteOwner_ne_timeout config.layout frame.interpretation.environment.act origin bytes.length before after created).elim
  | escape target carriers allocated | jump target kind allocated => simp only [created] at executed; cases executed
  | ok destination allocated =>
    simp only [created, buildExpr, timeout, EvalM.stop] at executed
    cases executed
    have fresh := newDestination_acceptedWorld config frame.interpretation.environment.act (.varr (.int .u8)) .value origin
      (some bytes.length) frame.initialized before after destination ambient types live regions pending world created
    obtain ⟨freshFrame⟩ := newDestination_fresh_frame config.layout frame.interpretation.environment.act (.varr (.int .u8)) .value origin
      (some bytes.length) before after destination world.ownership.source.structural.1.1.1 created
    exact ⟨destination, fresh, freshFrame.acceptedFrame source⟩

theorem execStmt_scopedByteOwner_timeout_world (typeFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context id scope scopeInst : Nat) (outer : List (Nat × Nat))
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) (before after : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (typingNext : TypingEnv) (typingAfter : Nat)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (typed : typeStatement (typeFuel + 1) frame.typing (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)
      frame.typingCounter = .ok (typingNext, typingAfter))
    (byteOwner : (frame.typing.variables[id]?).map (·.ty) = some (.varr (.int .u8)))
    (scopes : frame.interpretation.environment.scopes = (scope, scopeInst) :: outer)
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none)
    (executed : execStmt 1 config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .stop .timeout after) :
    ∃ destination, AcceptedWorld config frame.initialized after ambient types live
      (freshReceivingRegion before destination :: regions) pending ∧ AcceptedFrame config accepted frame after types := by
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
  exact execStmt_byteOwner_timeout_world config accepted frame id descriptor frame.source.impl before after root bytes origin bytesOrigin
    ambient types live regions pending world source runtimeDeclared descriptorType implementation unnamed resolved executed

theorem execStmt_acceptedByteOwner_timeout_world (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context id : Nat) (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId)
    (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (typingNext : TypingEnv) (typingAfter : Nat)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (typed : typeStatement frame.typingFuel frame.typing (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)
      frame.typingCounter = .ok (typingNext, typingAfter))
    (byteOwner : (frame.typing.variables[id]?).map (·.ty) = some (.varr (.int .u8)))
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none)
    (executed : execStmt 1 config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .stop .timeout after) :
    ∃ destination, AcceptedWorld config frame.initialized after ambient types live
      (freshReceivingRegion before destination :: regions) pending ∧ AcceptedFrame config accepted frame after types := by
  cases fuel : frame.typingFuel with
  | zero =>
    rw [fuel] at typed
    change Except.error _ = Except.ok _ at typed
    cases typed
  | succ typeFuel =>
    cases scopes : frame.interpretation.environment.scopes with
    | nil =>
      have impossible := executed
      simp only [execStmt] at impossible
      cases declared : frame.interpretation.environment.vars[id]? with
      | none => simp only [declared, fault, EvalM.stop] at impossible; cases impossible
      | some descriptor =>
        simp only [declared, rootOf, scopes, List.find?_nil, fault, EvalM.stop, bind] at impossible
        cases impossible
    | cons scopeEntry outer =>
      obtain ⟨scope, scopeInst⟩ := scopeEntry
      exact execStmt_scopedByteOwner_timeout_world typeFuel config accepted frame context id scope scopeInst outer bytes origin
        bytesOrigin before after ambient types live regions pending typingNext typingAfter world source phase
        (by simpa only [fuel] using typed) byteOwner scopes unnamed executed

#print axioms execStmt_acceptedByteOwner_timeout_world
#print axioms execStmt_byteOwner_timeout_world
#print axioms newDestination_byteOwner_ne_timeout
#print axioms evalValue_byteOwner_timeout_world

end Goose.Proofs.ConstructionAcceptedExecution

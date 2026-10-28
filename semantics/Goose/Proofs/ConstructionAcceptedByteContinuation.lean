import Goose.Proofs.ConstructionAcceptedLocalAdvance

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execStmt_scopedByteOwner_continuation (fuel typeFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context id scope scopeInst : Nat) (outer : List (Nat × Nat))
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) (before after : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (rootAfter : RState)
    (typingNext : TypingEnv) (typingAfter : Nat)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (rootChecked : rpStmt frame.source (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)
      frame.rootCursor = .ok ((), rootAfter))
    (typed : typeStatement (typeFuel + 1) frame.typing (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)
      frame.typingCounter = .ok (typingNext, typingAfter))
    (byteOwner : (frame.typing.variables[id]?).map (·.ty) = some (.varr (.int .u8)))
    (scopes : frame.interpretation.environment.scopes = (scope, scopeInst) :: outer)
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none)
    (executed : execStmt (fuel + 2) config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .ok (.normal .unit) after) :
    ∃ (stored : StoredValue) (published : ExecutionState),
      let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
      rootAfter = (advanceLocalFrame frame id).rootCursor ∧
      typingNext = (advanceLocalFrame frame id).typing ∧
      RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
      AcceptedWorld config frame.initialized after ambient (registerRootType types root (.varr (.int .u8)))
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending ∧
      AcceptedFrame config accepted (advanceLocalFrame frame id) after (registerRootType types root (.varr (.int .u8))) := by
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
  have rootOrder := (rpStmt_letS_initializer rootChecked).1
  let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
  have resolved : rootOf frame.interpretation.environment id before = .ok root before := by
    simp only [rootOf, runtimeDeclared, scopes, List.find?_cons, localScope', beq_self_eq_true, pure, root]
  have uninitialized : frame.rootCursor.nextVar ≤ id ∨ id ∈ frame.source.initializing :=
    Or.inl (by rw [rootOrder]; exact Nat.le_refl _)
  obtain ⟨fresh, freshType, freshSynthetic⟩ := source.uninitializedLocal_fresh id root uninitialized resolved
  have compatible : RootTypeCompatible types root (.varr (.int .u8)) := by
    intro previous present
    rw [source.uninitializedTypes id uninitialized root resolved] at present
    cases present
  have originFact := source.compatible.origin
  unfold SourceOrigin at originFact
  rw [phase] at originFact
  obtain ⟨original, calls, contextFound, implementationFound, implementationId, rest⟩ := originFact
  have implementation : config.module.impls[frame.interpretation.environment.implementation]? = some frame.source.impl := by
    rw [implementationId]
    exact implementationFound
  obtain ⟨stored, published, fits, ⟨publishedFrame⟩, publishedWorld, valueType, sampled, bound, extended, finalWorld⟩ :=
    execStmt_byteOwner_letWorld fuel config frame.initialized frame.interpretation.environment id descriptor frame.source.impl
      bytes origin bytesOrigin before after root ambient types live regions pending world runtimeDeclared descriptorType implementation
      unnamed resolved compatible True.intro fresh freshType freshSynthetic executed
  have sourceDeclared : frame.source.impl.vars[id]? = some descriptor := by
    rw [source.compatible.sourceVariables]
    exact declared
  have cursor := rpStmt_byteOwner_cursor frame.source id bytes origin bytesOrigin frame.rootCursor rootAfter descriptor
    sourceDeclared descriptorType fits rootChecked
  have typing := typeStatement_let_environment typeFuel frame.typing typingNext id
    (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin frame.typingCounter typingAfter typed
  have publishedSource := publishedFrame.acceptedFrame source
  have publishedResolved := rootOf_transfer frame.interpretation id before published root resolved
  have advanced := publishedSource.bindFreshStored_advance publishedWorld id descriptor root stored rootOrder typingOrder
    declared (valueType.trans descriptorType.symm) (by rw [descriptorType]; rfl) publishedResolved bound
  refine ⟨stored, published, ?_, ?_, extended, finalWorld, ?_⟩
  · simpa only [advanceLocalFrame] using cursor
  · simpa only [advanceLocalFrame] using typing
  · simpa only [descriptorType] using advanced

#print axioms execStmt_scopedByteOwner_continuation

end Goose.Proofs.ConstructionAcceptedExecution

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
      typingAfter = (advanceLocalFrame frame id).typingCounter ∧
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
  refine ⟨stored, published, ?_, ?_, ?_, extended, finalWorld, ?_⟩
  · simpa only [advanceLocalFrame] using cursor
  · simpa only [advanceLocalFrame] using typing
  · simpa only [advanceLocalFrame] using typeStatement_byteOwner_counter typeFuel frame.typing typingNext id bytes origin
      bytesOrigin frame.typingCounter typingAfter typed
  · simpa only [descriptorType] using advanced

theorem execStmt_byteOwner_continuation (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context id : Nat) (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId)
    (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (rootAfter : RState)
    (typingNext : TypingEnv) (typingAfter : Nat)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (rootChecked : rpStmt frame.source (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)
      frame.rootCursor = .ok ((), rootAfter))
    (typed : typeStatement frame.typingFuel frame.typing (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)
      frame.typingCounter = .ok (typingNext, typingAfter))
    (byteOwner : (frame.typing.variables[id]?).map (·.ty) = some (.varr (.int .u8)))
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none)
    (executed : execStmt (fuel + 2) config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .ok (.normal .unit) after) :
    ∃ (scopeInst : Nat) (stored : StoredValue) (published : ExecutionState),
      let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
      rootAfter = (advanceLocalFrame frame id).rootCursor ∧
      typingNext = (advanceLocalFrame frame id).typing ∧
      typingAfter = (advanceLocalFrame frame id).typingCounter ∧
      RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
      AcceptedWorld config frame.initialized after ambient (registerRootType types root (.varr (.int .u8)))
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending ∧
      AcceptedFrame config accepted (advanceLocalFrame frame id) after (registerRootType types root (.varr (.int .u8))) := by
  cases fuelCase : frame.typingFuel with
  | zero =>
    rw [fuelCase] at typed
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
      obtain ⟨stored, published, result⟩ := execStmt_scopedByteOwner_continuation fuel typeFuel config accepted frame
        context id scope scopeInst outer bytes origin bytesOrigin before after ambient types live regions pending rootAfter
        typingNext typingAfter world source phase rootChecked (by simpa only [fuelCase] using typed) byteOwner scopes unnamed executed
      exact ⟨scopeInst, stored, published, result⟩

theorem execStmt_entryByteOwner_continuation (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (id : Nat) (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId)
    (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (rootAfter : RState)
    (typingNext : TypingEnv) (typingAfter : Nat)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation config.module.entry)
    (rootChecked : rpStmt frame.source (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)
      frame.rootCursor = .ok ((), rootAfter))
    (typed : typeStatement frame.typingFuel frame.typing (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)
      frame.typingCounter = .ok (typingNext, typingAfter))
    (byteOwner : (frame.typing.variables[id]?).map (·.ty) = some (.varr (.int .u8)))
    (executed : execStmt (fuel + 2) config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .ok (.normal .unit) after) :
    ∃ (scopeInst : Nat) (stored : StoredValue) (published : ExecutionState),
      let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
      rootAfter = (advanceLocalFrame frame id).rootCursor ∧
      typingNext = (advanceLocalFrame frame id).typing ∧
      typingAfter = (advanceLocalFrame frame id).typingCounter ∧
      RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
      AcceptedWorld config frame.initialized after ambient (registerRootType types root (.varr (.int .u8)))
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending ∧
      AcceptedFrame config accepted (advanceLocalFrame frame id) after (registerRootType types root (.varr (.int .u8))) := by
  obtain ⟨entry, implementation, entryFound, implFound, paramsEmpty, resultsEmpty⟩ := validated_entry config.module accepted.accepted
  have originFact := source.compatible.origin
  unfold SourceOrigin at originFact
  rw [phase] at originFact
  obtain ⟨actual, calls, actualFound, actualImpl, rest⟩ := originFact
  have same : actual = entry := Option.some.inj (actualFound.symm.trans entryFound)
  subst actual
  have sameImpl : frame.source.impl = implementation := Option.some.inj (actualImpl.symm.trans implFound)
  have unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none := by
    simp only [sameImpl, resultsEmpty, Array.toList_empty, List.zipIdx_nil, List.find?_nil]
  exact execStmt_byteOwner_continuation fuel config accepted frame config.module.entry id bytes origin bytesOrigin before after
    ambient types live regions pending rootAfter typingNext typingAfter world source phase rootChecked typed byteOwner unnamed executed

#print axioms execStmt_scopedByteOwner_continuation
#print axioms execStmt_byteOwner_continuation
#print axioms execStmt_entryByteOwner_continuation

end Goose.Proofs.ConstructionAcceptedExecution

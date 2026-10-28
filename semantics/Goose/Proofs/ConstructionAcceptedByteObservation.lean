import Goose.Proofs.ConstructionAcceptedByteContinuation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execStmt_scopedByteOwner_observation (fuel typeFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
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
      Nonempty (FreshDestinationFrame before published) ∧
      bindRoot (.local frame.interpretation.environment.act scopeInst id) (.stored stored) published = .ok () after := by
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
  obtain ⟨stored, published, fits, publishedFrame, publishedWorld, valueType, sampled, bound, extended, finalWorld⟩ :=
    execStmt_byteOwner_letWorld fuel config frame.initialized frame.interpretation.environment id descriptor frame.source.impl
      bytes origin bytesOrigin before after root ambient types live regions pending world runtimeDeclared descriptorType implementation
      unnamed resolved compatible True.intro fresh freshType freshSynthetic executed
  exact ⟨stored, published, publishedFrame, bound⟩

theorem execStmt_byteOwner_observation (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
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
      Nonempty (FreshDestinationFrame before published) ∧
      bindRoot (.local frame.interpretation.environment.act scopeInst id) (.stored stored) published = .ok () after := by
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
      obtain ⟨stored, published, result⟩ := execStmt_scopedByteOwner_observation fuel typeFuel config accepted frame
        context id scope scopeInst outer bytes origin bytesOrigin before after ambient types live regions pending rootAfter
        typingNext typingAfter world source phase rootChecked (by simpa only [fuelCase] using typed) byteOwner scopes unnamed executed
      exact ⟨scopeInst, stored, published, result⟩

theorem freshDestination_bindRoot_outside (before published after : ExecutionState)
    (root other : Goose.Core.RootInst) (stored : StoredValue)
    (frame : FreshDestinationFrame before published)
    (bound : bindRoot root (.stored stored) published = .ok () after)
    (different : other ≠ root) :
    after.objects.lookup other = before.objects.lookup other ∧
    after.objectOrdinals.lookup other = before.objectOrdinals.lookup other := by
  constructor
  · rw [bindRoot_lookup_other root other (.stored stored) published after bound different, frame.outer]
  · rw [bindRoot_ordinals_other root other (.stored stored) published after bound different, frame.outer]

theorem execStmt_byteOwner_outside (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
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
    ∀ other, (∀ scope id, other ≠ .local frame.interpretation.environment.act scope id) →
      after.objects.lookup other = before.objects.lookup other ∧
      after.objectOrdinals.lookup other = before.objectOrdinals.lookup other := by
  intro other outside
  obtain ⟨scopeInst, stored, published, ⟨publishedFrame⟩, bound⟩ :=
    execStmt_byteOwner_observation fuel config accepted frame context id bytes origin bytesOrigin before after
      ambient types live regions pending rootAfter typingNext typingAfter world source phase rootChecked typed byteOwner unnamed executed
  exact freshDestination_bindRoot_outside before published after _ other stored publishedFrame bound (outside scopeInst id)

#print axioms execStmt_byteOwner_outside
#print axioms execStmt_byteOwner_observation
#print axioms freshDestination_bindRoot_outside
#print axioms execStmt_scopedByteOwner_observation

end Goose.Proofs.ConstructionAcceptedExecution

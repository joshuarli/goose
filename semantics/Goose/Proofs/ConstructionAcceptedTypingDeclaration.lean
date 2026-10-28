import Goose.Proofs.ConstructionAcceptedScopeTypes

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem typeStatement_let_descriptor (fuel : Nat) (env next : TypingEnv) (id : Nat)
    (expression : Expr) (origin before after : Nat)
    (checked : typeStatement (fuel + 1) env (.letS id expression origin) before = .ok (next, after)) :
    ∃ descriptor, env.variables[id]? = some descriptor ∧ descriptor.scope = env.scope := by
  simp only [typeStatement, bind, StateT.bind] at checked
  change Except.bind (((do
    let expected ← get
    if id != expected then throw ⟨.type, "variables must be declared once in ascending order"⟩
    let some localVar := env.variables[id]? | throw ⟨.type, "declared localVar outside table"⟩
    if localVar.scope != env.scope || !localVar.ty.storable then throw ⟨.type, "localVar scope or type mismatch"⟩
    set (expected + 1)
    pure localVar) : TypingM LocalVar) before) _ = _ at checked
  have getState (state : Nat) : (get : TypingM Nat) state = .ok (state, state) := rfl
  have throwState {α : Type} (error : Goose.Core.Rejection) (state : Nat) :
      (throw error : TypingM α) state = .error error := rfl
  simp only [bind, StateT.bind, getState, Except.bind] at checked
  by_cases ordered : id = before
  · subst before
    cases present : env.variables[id]? with
    | none =>
      simp [present, throwState] at checked
    | some descriptor =>
      by_cases same : descriptor.scope = env.scope
      · exact ⟨descriptor, rfl, same⟩
      · simp [StateT.bind, present, same, throwState] at checked
        change Except.error _ = Except.ok _ at checked
        cases checked
  · simp [StateT.bind, ordered, throwState] at checked
    change Except.error _ = Except.ok _ at checked
    cases checked

theorem typeStatement_let_environment (fuel : Nat) (env next : TypingEnv) (id : Nat)
    (expression : Expr) (origin before after : Nat)
    (checked : typeStatement (fuel + 1) env (.letS id expression origin) before = .ok (next, after)) :
    next = { env with visible := id :: env.visible } := by
  simp only [typeStatement, bind, StateT.bind, Except.bind] at checked
  repeat' split at checked
  all_goals try cases checked
  all_goals rfl

theorem execStmt_typedScopedByteOwner_letWorld (fuel typeFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context localVar scope scopeInst : Nat) (outer : List (Nat × Nat))
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) (before after : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (rootAfter : RState)
    (typingNext : TypingEnv) (typingAfter : Nat)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (rootChecked : rpStmt frame.source (.letS localVar (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)
      frame.rootCursor = .ok ((), rootAfter))
    (typed : typeStatement (typeFuel + 1) frame.typing (.letS localVar (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)
      frame.typingCounter = .ok (typingNext, typingAfter))
    (byteOwner : (frame.typing.variables[localVar]?).map (·.ty) = some (.varr (.int .u8)))
    (scopes : frame.interpretation.environment.scopes = (scope, scopeInst) :: outer)
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some localVar)) = none)
    (executed : execStmt (fuel + 2) config frame.interpretation.environment
      (.letS localVar (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .ok (.normal .unit) after) :
    ∃ (stored : StoredValue) (published : ExecutionState),
      RootTypesExtend types (registerRootType types (.local frame.interpretation.environment.act scopeInst localVar) (.varr (.int .u8))) ∧
      AcceptedWorld config frame.initialized after ambient
        (registerRootType types (.local frame.interpretation.environment.act scopeInst localVar) (.varr (.int .u8)))
        (fun other => other = .local frame.interpretation.environment.act scopeInst localVar ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending := by
  obtain ⟨descriptor, declared, localScope⟩ := typeStatement_let_descriptor typeFuel frame.typing typingNext localVar
    (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin frame.typingCounter typingAfter typed
  have descriptorType : descriptor.ty = .varr (.int .u8) := by
    simpa only [declared, Option.map_some, Option.some.injEq] using byteOwner
  have sourceScopes : frame.source.scopes = scope :: outer.map Prod.fst := by
    rw [source.compatible.scopes, scopes]
    rfl
  have currentScope := source.compatible.currentScope scope (outer.map Prod.fst) sourceScopes
  have actualScope : descriptor.scope = scope := localScope.trans currentScope
  have runtimeDeclared : frame.interpretation.environment.vars[localVar]? = some descriptor := by
    rw [source.compatible.variables]
    exact declared
  exact execStmt_scopedByteOwner_letWorld fuel config accepted frame context localVar scope scopeInst outer descriptor
    bytes origin bytesOrigin before after ambient types live regions pending rootAfter world source phase rootChecked
    runtimeDeclared descriptorType actualScope scopes unnamed executed

theorem execStmt_typedByteOwner_letWorld (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context localVar : Nat) (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId)
    (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (rootAfter : RState)
    (typingNext : TypingEnv) (typingAfter : Nat)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (rootChecked : rpStmt frame.source (.letS localVar (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)
      frame.rootCursor = .ok ((), rootAfter))
    (typed : typeStatement frame.typingFuel frame.typing (.letS localVar (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)
      frame.typingCounter = .ok (typingNext, typingAfter))
    (byteOwner : (frame.typing.variables[localVar]?).map (·.ty) = some (.varr (.int .u8)))
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some localVar)) = none)
    (executed : execStmt (fuel + 2) config frame.interpretation.environment
      (.letS localVar (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .ok (.normal .unit) after) :
    ∃ (scopeInst : Nat) (stored : StoredValue) (published : ExecutionState),
      RootTypesExtend types (registerRootType types (.local frame.interpretation.environment.act scopeInst localVar) (.varr (.int .u8))) ∧
      AcceptedWorld config frame.initialized after ambient
        (registerRootType types (.local frame.interpretation.environment.act scopeInst localVar) (.varr (.int .u8)))
        (fun other => other = .local frame.interpretation.environment.act scopeInst localVar ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending := by
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
    cases declared : frame.interpretation.environment.vars[localVar]? with
    | none => simp only [declared, fault, EvalM.stop] at impossible; cases impossible
    | some descriptor =>
      simp only [declared, rootOf, scopes, List.find?_nil, fault, EvalM.stop, bind] at impossible
      cases impossible
   | cons scopeEntry outer =>
    obtain ⟨scope, scopeInst⟩ := scopeEntry
    obtain ⟨stored, published, extended, preserved⟩ := execStmt_typedScopedByteOwner_letWorld fuel typeFuel config accepted frame
      context localVar scope scopeInst outer bytes origin bytesOrigin before after ambient types live regions pending rootAfter typingNext
      typingAfter world source phase rootChecked (by simpa only [fuelCase] using typed) byteOwner scopes unnamed executed
    exact ⟨scopeInst, stored, published, extended, preserved⟩

theorem execStmt_entryByteOwner_letWorld (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (localVar : Nat) (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId)
    (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (rootAfter : RState)
    (typingNext : TypingEnv) (typingAfter : Nat)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation config.module.entry)
    (rootChecked : rpStmt frame.source (.letS localVar (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)
      frame.rootCursor = .ok ((), rootAfter))
    (typed : typeStatement frame.typingFuel frame.typing (.letS localVar (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)
      frame.typingCounter = .ok (typingNext, typingAfter))
    (byteOwner : (frame.typing.variables[localVar]?).map (·.ty) = some (.varr (.int .u8)))
    (executed : execStmt (fuel + 2) config frame.interpretation.environment
      (.letS localVar (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .ok (.normal .unit) after) :
    ∃ (scopeInst : Nat) (stored : StoredValue) (published : ExecutionState),
      RootTypesExtend types (registerRootType types (.local frame.interpretation.environment.act scopeInst localVar) (.varr (.int .u8))) ∧
      AcceptedWorld config frame.initialized after ambient
        (registerRootType types (.local frame.interpretation.environment.act scopeInst localVar) (.varr (.int .u8)))
        (fun other => other = .local frame.interpretation.environment.act scopeInst localVar ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending := by
  obtain ⟨entry, implementation, entryFound, implFound, paramsEmpty, resultsEmpty⟩ := validated_entry config.module accepted.accepted
  have originFact := source.compatible.origin
  unfold SourceOrigin at originFact
  rw [phase] at originFact
  obtain ⟨actual, calls, actualFound, actualImpl, rest⟩ := originFact
  have same : actual = entry := Option.some.inj (actualFound.symm.trans entryFound)
  subst actual
  have sameImpl : frame.source.impl = implementation := Option.some.inj (actualImpl.symm.trans implFound)
  have unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some localVar)) = none := by
    simp only [sameImpl, resultsEmpty, Array.toList_empty, List.zipIdx_nil, List.find?_nil]
  exact execStmt_typedByteOwner_letWorld fuel config accepted frame config.module.entry localVar bytes origin bytesOrigin before after
    ambient types live regions pending rootAfter typingNext typingAfter world source phase rootChecked typed byteOwner unnamed executed

#print axioms typeStatement_let_descriptor
#print axioms typeStatement_let_environment
#print axioms execStmt_typedScopedByteOwner_letWorld
#print axioms execStmt_typedByteOwner_letWorld
#print axioms execStmt_entryByteOwner_letWorld

end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionAcceptedScopeTypes

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

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

theorem execStmt_typedScopedByteOwner_letWorld (fuel typeFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context localVar scope scopeInst : Nat) (outer : List (Nat × Nat))
    (bytes : List UInt8) (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (rootAfter : RState)
    (typingNext : TypingEnv) (typingAfter : Nat)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (rootChecked : rpStmt frame.source (.letS localVar (.bytes (.varr (.int .u8)) bytes origin) origin)
      frame.rootCursor = .ok ((), rootAfter))
    (typed : typeStatement (typeFuel + 1) frame.typing (.letS localVar (.bytes (.varr (.int .u8)) bytes origin) origin)
      frame.typingCounter = .ok (typingNext, typingAfter))
    (byteOwner : (frame.typing.variables[localVar]?).map (·.ty) = some (.varr (.int .u8)))
    (scopes : frame.interpretation.environment.scopes = (scope, scopeInst) :: outer)
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some localVar)) = none)
    (executed : execStmt (fuel + 2) config frame.interpretation.environment
      (.letS localVar (.bytes (.varr (.int .u8)) bytes origin) origin) before = .ok (.normal .unit) after) :
    ∃ (stored : StoredValue) (published : ExecutionState),
      RootTypesExtend types (registerRootType types (.local frame.interpretation.environment.act scopeInst localVar) (.varr (.int .u8))) ∧
      AcceptedWorld config frame.initialized after ambient
        (registerRootType types (.local frame.interpretation.environment.act scopeInst localVar) (.varr (.int .u8)))
        (fun other => other = .local frame.interpretation.environment.act scopeInst localVar ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending := by
  obtain ⟨descriptor, declared, localScope⟩ := typeStatement_let_descriptor typeFuel frame.typing typingNext localVar
    (.bytes (.varr (.int .u8)) bytes origin) origin frame.typingCounter typingAfter typed
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
    bytes origin before after ambient types live regions pending rootAfter world source phase rootChecked
    runtimeDeclared descriptorType actualScope scopes unnamed executed

#print axioms typeStatement_let_descriptor
#print axioms execStmt_typedScopedByteOwner_letWorld

end Goose.Proofs.ConstructionAcceptedExecution

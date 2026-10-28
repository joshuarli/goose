import Goose.Proofs.ConstructionAcceptedByteStatement
import Goose.Proofs.ConstructionRootCorrespondenceCursors

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem AcceptedFrame.enterScope_frontier {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (scope : Nat) :
    ∀ entry ∈ (scope, state.nextScope) :: frame.interpretation.environment.scopes,
      entry.2 < state.nextScope + 1 := by
  intro entry member
  rcases List.mem_cons.mp member with same | earlier
  · subst entry
    exact Nat.lt_succ_self _
  · exact Nat.lt_trans (source.scopeFrontier entry earlier) (Nat.lt_succ_self _)

theorem AcceptedFrame.uninitializedLocal_fresh {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (id : Nat) (root : Goose.Core.RootInst)
    (uninitialized : frame.rootCursor.nextVar ≤ id ∨ id ∈ frame.source.initializing)
    (resolved : rootOf frame.interpretation.environment id state = .ok root state) :
    state.objectOrdinals.lookup root = none ∧
      (∀ act scope varId, root = .local act scope varId → act < state.nextAct ∧ scope < state.nextScope) ∧
      (∀ global, root = .global global → config.module.globals.size ≤ global →
        global < config.module.globals.size + state.nextScope) := by
  obtain ⟨_, absent⟩ := source.uninitializedLocals id uninitialized root resolved
  have scopeBound : ∀ scope, root = .local frame.interpretation.environment.act scope id → scope < state.nextScope := by
    intro scope same
    have actual := rootOf_instantiates frame.interpretation id state root resolved
    cases actual with
    | «local» id descriptor actual declared active =>
      have equal : actual = scope := by cases same; rfl
      subst actual
      exact source.scopeFrontier (descriptor.scope, scope) (List.mem_of_find?_eq_some active)
  obtain ⟨scope, same⟩ := rootOf_variable frame.interpretation id state root resolved
  refine ⟨absent, ?_, ?_⟩
  · intro act actual varId equal
    rw [same] at equal
    cases equal
    exact ⟨source.frontier.1, scopeBound scope same⟩
  · intro global equal
    rw [same] at equal
    cases equal

theorem execStmt_checkedByteOwner_letWorld (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (localVar : Nat) (descriptor : LocalVar) (implementation : Impl)
    (bytes : List UInt8) (origin : Goose.Core.OriginId) (before after : ExecutionState) (root : Goose.Core.RootInst)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (declared : frame.interpretation.environment.vars[localVar]? = some descriptor)
    (ty : descriptor.ty = .varr (.int .u8))
    (implementationFound : config.module.impls[frame.interpretation.environment.implementation]? = some implementation)
    (unnamed : (implementation.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some localVar)) = none)
    (uninitialized : frame.rootCursor.nextVar ≤ localVar ∨ localVar ∈ frame.source.initializing)
    (resolved : rootOf frame.interpretation.environment localVar before = .ok root before)
    (executed : execStmt (fuel + 2) config frame.interpretation.environment
      (.letS localVar (.bytes (.varr (.int .u8)) bytes origin) origin) before = .ok (.normal .unit) after) :
    ∃ (stored : StoredValue) (published : ExecutionState),
      RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
      AcceptedWorld config frame.initialized after ambient (registerRootType types root (.varr (.int .u8)))
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending := by
  obtain ⟨fresh, freshType, freshSynthetic⟩ := source.uninitializedLocal_fresh localVar root uninitialized resolved
  have compatible : RootTypeCompatible types root (.varr (.int .u8)) := by
    intro previous present
    rw [source.uninitializedTypes localVar uninitialized root resolved] at present
    cases present
  exact execStmt_byteOwner_letWorld fuel config frame.initialized frame.interpretation.environment localVar descriptor
    implementation bytes origin before after root ambient types live regions pending world declared ty implementationFound
    unnamed resolved compatible True.intro fresh freshType freshSynthetic executed

theorem execStmt_rootCheckedByteOwner_letWorld (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (localVar : Nat) (descriptor : LocalVar) (implementation : Impl)
    (bytes : List UInt8) (origin : Goose.Core.OriginId) (before after : ExecutionState) (root : Goose.Core.RootInst)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (rootAfter : RState)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (checked : rpStmt frame.source (.letS localVar (.bytes (.varr (.int .u8)) bytes origin) origin)
      frame.rootCursor = .ok ((), rootAfter))
    (declared : frame.interpretation.environment.vars[localVar]? = some descriptor)
    (ty : descriptor.ty = .varr (.int .u8))
    (implementationFound : config.module.impls[frame.interpretation.environment.implementation]? = some implementation)
    (unnamed : (implementation.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some localVar)) = none)
    (resolved : rootOf frame.interpretation.environment localVar before = .ok root before)
    (executed : execStmt (fuel + 2) config frame.interpretation.environment
      (.letS localVar (.bytes (.varr (.int .u8)) bytes origin) origin) before = .ok (.normal .unit) after) :
    ∃ (stored : StoredValue) (published : ExecutionState),
      RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
      AcceptedWorld config frame.initialized after ambient (registerRootType types root (.varr (.int .u8)))
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending := by
  have order := (rpStmt_letS_initializer checked).1
  exact execStmt_checkedByteOwner_letWorld fuel config accepted frame localVar descriptor implementation bytes origin
    before after root ambient types live regions pending world source declared ty implementationFound unnamed
    (Or.inl (by rw [order]; exact Nat.le_refl _)) resolved executed

theorem execStmt_implementationByteOwner_letWorld (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context localVar : Nat) (descriptor : LocalVar)
    (bytes : List UInt8) (origin : Goose.Core.OriginId) (before after : ExecutionState) (root : Goose.Core.RootInst)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (rootAfter : RState)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (checked : rpStmt frame.source (.letS localVar (.bytes (.varr (.int .u8)) bytes origin) origin)
      frame.rootCursor = .ok ((), rootAfter))
    (declared : frame.interpretation.environment.vars[localVar]? = some descriptor)
    (ty : descriptor.ty = .varr (.int .u8))
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some localVar)) = none)
    (resolved : rootOf frame.interpretation.environment localVar before = .ok root before)
    (executed : execStmt (fuel + 2) config frame.interpretation.environment
      (.letS localVar (.bytes (.varr (.int .u8)) bytes origin) origin) before = .ok (.normal .unit) after) :
    ∃ (stored : StoredValue) (published : ExecutionState),
      RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
      AcceptedWorld config frame.initialized after ambient (registerRootType types root (.varr (.int .u8)))
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending := by
  have originFact := source.compatible.origin
  unfold SourceOrigin at originFact
  rw [phase] at originFact
  obtain ⟨original, calls, contextFound, implementationFound, implementationId, rest⟩ := originFact
  have implementation : config.module.impls[frame.interpretation.environment.implementation]? = some frame.source.impl := by
    rw [implementationId]
    exact implementationFound
  exact execStmt_rootCheckedByteOwner_letWorld fuel config accepted frame localVar descriptor frame.source.impl
    bytes origin before after root ambient types live regions pending rootAfter world source checked declared ty
    implementation unnamed resolved executed

theorem execStmt_scopedByteOwner_letWorld (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context localVar scope scopeInst : Nat) (outer : List (Nat × Nat))
    (descriptor : LocalVar) (bytes : List UInt8) (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (rootAfter : RState)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (checked : rpStmt frame.source (.letS localVar (.bytes (.varr (.int .u8)) bytes origin) origin)
      frame.rootCursor = .ok ((), rootAfter))
    (declared : frame.interpretation.environment.vars[localVar]? = some descriptor)
    (ty : descriptor.ty = .varr (.int .u8)) (scopeType : descriptor.scope = scope)
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
  have resolved : rootOf frame.interpretation.environment localVar before =
      .ok (.local frame.interpretation.environment.act scopeInst localVar) before := by
    simp only [rootOf, declared, scopes, List.find?_cons, scopeType, beq_self_eq_true, pure]
  exact execStmt_implementationByteOwner_letWorld fuel config accepted frame context localVar descriptor bytes origin before after
    (.local frame.interpretation.environment.act scopeInst localVar) ambient types live regions pending rootAfter
    world source phase checked declared ty unnamed resolved executed

#print axioms AcceptedFrame.enterScope_frontier
#print axioms AcceptedFrame.uninitializedLocal_fresh
#print axioms execStmt_checkedByteOwner_letWorld
#print axioms execStmt_rootCheckedByteOwner_letWorld
#print axioms execStmt_implementationByteOwner_letWorld
#print axioms execStmt_scopedByteOwner_letWorld

end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionAcceptedByteStatement

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

#print axioms AcceptedFrame.enterScope_frontier
#print axioms AcceptedFrame.uninitializedLocal_fresh
#print axioms execStmt_checkedByteOwner_letWorld

end Goose.Proofs.ConstructionAcceptedExecution

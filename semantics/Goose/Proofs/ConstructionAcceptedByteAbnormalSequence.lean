import Goose.Proofs.ConstructionAcceptedByteExecutionSequence

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execStmt_acceptedByteOwner_flow (runFuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context id : Nat) (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId)
    (rest : List Stmt) (before after : ExecutionState) (flow : Flow) (types : RootTypes)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (position : SourcePosition accepted frame (.statements (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin :: rest)))
    (nesting : frame.typingFuel = checkFuel + 1)
    (byteOwner : (frame.typing.variables[id]?).map (·.ty) = some (.varr (.int .u8)))
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none)
    (head : execStmt (runFuel + 2) config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .ok flow after) :
    flow = .normal .unit := by
  let statement := Stmt.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin
  have headPosition := position.statements_head accepted frame statement rest checkFuel nesting
  obtain ⟨typingNext, typingAfter, rootsAfter, typed, rooted⟩ := headPosition.checked accepted _ _
  cases checkFuel with
  | zero =>
    change Except.error _ = Except.ok _ at typed
    cases typed
  | succ checkFuel =>
    obtain ⟨descriptor, declared, localScope, order⟩ := typeStatement_let_descriptor checkFuel frame.typing typingNext id
      (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin frame.typingCounter typingAfter typed
    have descriptorType : descriptor.ty = .varr (.int .u8) := by
      simpa only [declared, Option.map_some, Option.some.injEq] using byteOwner
    have runtimeDeclared : frame.interpretation.environment.vars[id]? = some descriptor := by
      rw [source.compatible.variables]
      exact declared
    have originFact := source.compatible.origin
    unfold SourceOrigin at originFact
    rw [phase] at originFact
    obtain ⟨original, calls, contextFound, implementationFound, implementationId, restOrigin⟩ := originFact
    have implementation : config.module.impls[frame.interpretation.environment.implementation]? = some frame.source.impl := by
      rw [implementationId]
      exact implementationFound
    cases scopes : frame.interpretation.environment.scopes with
    | nil =>
      have impossible := head
      simp only [execStmt, runtimeDeclared, rootOf, scopes, List.find?_nil, fault, EvalM.stop, bind] at impossible
      cases impossible
    | cons scopeEntry outer =>
      obtain ⟨scope, scopeInst⟩ := scopeEntry
      have sourceScopes : frame.source.scopes = scope :: outer.map Prod.fst := by
        rw [source.compatible.scopes, scopes]
        rfl
      have localScope' := localScope.trans (source.compatible.currentScope scope (outer.map Prod.fst) sourceScopes)
      let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
      have resolved : rootOf frame.interpretation.environment id before = .ok root before := by
        simp only [rootOf, runtimeDeclared, scopes, List.find?_cons, localScope', beq_self_eq_true, pure, root]
      exact execStmt_byteOwner_flow runFuel config frame.interpretation.environment id descriptor frame.source.impl root
        bytes origin bytesOrigin before after flow runtimeDeclared descriptorType implementation unnamed resolved head

theorem execStmts_byteOwner_completedHead (runFuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context id : Nat) (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId)
    (rest : List Stmt) (before middle : ExecutionState) (flow : Flow) (result : ExecutionStep Flow)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (position : SourcePosition accepted frame (.statements (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin :: rest)))
    (nesting : frame.typingFuel = checkFuel + 1)
    (byteOwner : (frame.typing.variables[id]?).map (·.ty) = some (.varr (.int .u8)))
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none)
    (head : execStmt (runFuel + 2) config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .ok flow middle)
    (executed : execStmts (runFuel + 3) config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin :: rest) before = result) :
    ∃ (scopeInst : Nat) (stored : StoredValue) (published : ExecutionState),
      let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
      let next := advanceLocalFrame { frame with typingFuel := checkFuel } id
      execStmts (runFuel + 2) config frame.interpretation.environment rest middle = result ∧
      RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
      AcceptedWorld config frame.initialized middle ambient (registerRootType types root (.varr (.int .u8)))
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending ∧
      AcceptedFrame config accepted next middle (registerRootType types root (.varr (.int .u8))) ∧
      SourcePosition accepted next (.statements rest) := by
  have normal := execStmt_acceptedByteOwner_flow runFuel checkFuel config accepted frame context id bytes origin bytesOrigin rest
    before middle flow types source phase position nesting byteOwner unnamed head
  subst flow
  simp only [execStmts, bind, head] at executed
  obtain ⟨scopeInst, stored, published, extended, finalWorld, finalSource, tailPosition⟩ :=
    execStmt_byteOwner_statementsTail runFuel checkFuel config accepted frame context id bytes origin bytesOrigin rest
      before middle ambient types live regions pending world source phase position nesting byteOwner unnamed head
  exact ⟨scopeInst, stored, published, executed, extended, finalWorld, finalSource, tailPosition⟩

theorem execStmts_byteOwner_split (runFuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context id : Nat) (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId)
    (rest : List Stmt) (before : ExecutionState) (result : ExecutionStep Flow)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (position : SourcePosition accepted frame (.statements (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin :: rest)))
    (nesting : frame.typingFuel = checkFuel + 1)
    (byteOwner : (frame.typing.variables[id]?).map (·.ty) = some (.varr (.int .u8)))
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none)
    (executed : execStmts (runFuel + 3) config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin :: rest) before = result) :
    execStmt (runFuel + 2) config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = result ∨
    ∃ (middle : ExecutionState) (scopeInst : Nat) (stored : StoredValue) (published : ExecutionState),
      let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
      let next := advanceLocalFrame { frame with typingFuel := checkFuel } id
      execStmts (runFuel + 2) config frame.interpretation.environment rest middle = result ∧
      RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
      AcceptedWorld config frame.initialized middle ambient (registerRootType types root (.varr (.int .u8)))
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending ∧
      AcceptedFrame config accepted next middle (registerRootType types root (.varr (.int .u8))) ∧
      SourcePosition accepted next (.statements rest) := by
  cases head : execStmt (runFuel + 2) config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before with
  | stop reason state | escape reason carriers state | jump reason kind state =>
    left
    simp only [execStmts, bind, head] at executed
    exact executed
  | ok flow middle =>
    right
    obtain ⟨scopeInst, stored, published, tail, extended, finalWorld, finalSource, tailPosition⟩ :=
      execStmts_byteOwner_completedHead runFuel checkFuel config accepted frame context id bytes origin bytesOrigin rest
        before middle flow result ambient types live regions pending world source phase position nesting byteOwner unnamed head executed
    exact ⟨middle, scopeInst, stored, published, tail, extended, finalWorld, finalSource, tailPosition⟩

#print axioms execStmt_acceptedByteOwner_flow
#print axioms execStmts_byteOwner_completedHead
#print axioms execStmts_byteOwner_split

end Goose.Proofs.ConstructionAcceptedExecution

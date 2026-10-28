import Goose.Proofs.ConstructionAcceptedByteSequence

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execStmt_byteOwner_flow (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation) (id : Nat) (descriptor : LocalVar) (implementation : Impl) (root : Goose.Core.RootInst) (bytes : List UInt8) (origin bytesOrigin : Nat) (before after : ExecutionState) (flow : Flow)
    (declared : environment.vars[id]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (unnamed : (implementation.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none)
    (resolved : rootOf environment id before = .ok root before)
    (executed : execStmt (fuel + 2) config environment (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .ok flow after) : flow = .normal .unit := by
  simp only [execStmt, declared, ty, Ty.nonfixed, implementationFound, unnamed, ordinaryProducerCount?,
    producerCount?, literalCount, Option.isSome_some, ↓reduceIte, materializeProducer, bind, pure, resolved,
    Option.isNone_none, Option.isSome_none, Option.map_none] at executed
  simp only [Bool.false_eq_true, ↓reduceIte, Option.orElse_eq_orElse, Option.orElse] at executed
  cases created : newDestination config.layout environment.act (.varr (.int .u8)) .value origin none (some bytes.length) before with
  | stop reason state | escape reason carriers state | jump reason kind state => simp only [created] at executed; cases executed
  | ok destination allocated =>
    simp only [created] at executed
    cases built : buildExpr (fuel + 1) config environment destination (.bytes (.varr (.int .u8)) bytes bytesOrigin) allocated with
    | stop reason state | escape reason carriers state | jump reason kind state => simp only [built] at executed; cases executed
    | ok _ state =>
      simp only [built] at executed
      cases completed : completedReceivingDestination destination state with
      | stop reason state | escape reason carriers state | jump reason kind state => simp only [completed] at executed; cases executed
      | ok selected ready =>
        simp only [completed] at executed
        cases published : publishCarriers origin [.completed selected] ready with
        | stop reason state | escape reason carriers state | jump reason kind state => simp only [published] at executed; cases executed
        | ok _ final =>
          simp only [published] at executed
          cases sampled : storedDestination selected final with
          | stop reason state | escape reason carriers state | jump reason kind state => simp only [sampled] at executed; cases executed
          | ok stored found =>
            simp only [sampled] at executed
            cases bound : bindRoot root (.stored { stored with ty := .varr (.int .u8), object := none }) found with
            | stop reason state | escape reason carriers state | jump reason kind state => simp only [bound] at executed; cases executed
            | ok _ last => simp only [bound] at executed; cases executed; rfl

theorem execStmts_normal_head (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (statement : Stmt) (rest : List Stmt) (before after : ExecutionState) (result : Value)
    (executed : execStmts (fuel + 1) config environment (statement :: rest) before = .ok (.normal result) after) :
    ∃ value middle, execStmt fuel config environment statement before = .ok (.normal value) middle ∧
      execStmts fuel config environment rest middle = .ok (.normal result) after := by
  simp only [execStmts, bind] at executed
  cases first : execStmt fuel config environment statement before with
  | stop reason state | escape reason carriers state | jump reason kind state =>
    simp only [first] at executed
    cases executed
  | ok flow middle =>
    cases flow with
    | normal value =>
      exact ⟨value, middle, rfl, by simpa only [first] using executed⟩
    | breaking | continuing =>
      simp only [first, pure] at executed
      cases executed

theorem execStmts_byteOwner_normalTail (runFuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context id : Nat) (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId)
    (rest : List Stmt) (before after : ExecutionState) (result : Value) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (position : SourcePosition accepted frame (.statements (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin :: rest)))
    (nesting : frame.typingFuel = checkFuel + 1)
    (byteOwner : (frame.typing.variables[id]?).map (·.ty) = some (.varr (.int .u8)))
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none)
    (executed : execStmts (runFuel + 3) config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin :: rest) before = .ok (.normal result) after) :
    ∃ (middle : ExecutionState) (scopeInst : Nat) (stored : StoredValue) (published : ExecutionState),
      let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
      let next := advanceLocalFrame { frame with typingFuel := checkFuel } id
      execStmts (runFuel + 2) config frame.interpretation.environment rest middle = .ok (.normal result) after ∧
      RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
      AcceptedWorld config frame.initialized middle ambient (registerRootType types root (.varr (.int .u8)))
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending ∧
      AcceptedFrame config accepted next middle (registerRootType types root (.varr (.int .u8))) ∧
      SourcePosition accepted next (.statements rest) := by
  let statement := Stmt.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin
  obtain ⟨value, middle, head, tail⟩ := execStmts_normal_head (runFuel + 2) config frame.interpretation.environment
    statement rest before after result executed
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
      dsimp only [statement] at impossible
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
      have flow := execStmt_byteOwner_flow runFuel config frame.interpretation.environment id descriptor frame.source.impl root
        bytes origin bytesOrigin before middle (.normal value) runtimeDeclared descriptorType implementation unnamed resolved head
      cases flow
      obtain ⟨scopeInst', stored, published, extended, finalWorld, finalSource, tailPosition⟩ :=
        execStmt_byteOwner_statementsTail runFuel (checkFuel + 1) config accepted frame context id bytes origin bytesOrigin rest
          before middle ambient types live regions pending world source phase position nesting byteOwner unnamed head
      exact ⟨middle, scopeInst', stored, published, tail, extended, finalWorld, finalSource, tailPosition⟩

#print axioms execStmt_byteOwner_flow
#print axioms execStmts_normal_head
#print axioms execStmts_byteOwner_normalTail

end Goose.Proofs.ConstructionAcceptedExecution

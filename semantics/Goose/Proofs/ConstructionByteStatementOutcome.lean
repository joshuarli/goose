import Goose.Proofs.ConstructionByteStatementStopped
import Goose.Proofs.ConstructionAcceptedByteAbnormalSequence

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

private theorem byteStatement_one_not_ok (config : EvalConfig) (environment : RuntimeActivation)
    (id : Nat) (descriptor : LocalVar) (implementation : Impl) (root : Goose.Core.RootInst)
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) (before after : ExecutionState) (flow : Flow)
    (declared : environment.vars[id]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (unnamed : (implementation.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none)
    (resolved : rootOf environment id before = .ok root before)
    (executed : execStmt 1 config environment (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .ok flow after) : False := by
  simp only [execStmt, declared, ty, Ty.nonfixed, implementationFound, unnamed, ordinaryProducerCount?,
    producerCount?, literalCount, Option.isSome_some, ↓reduceIte, materializeProducer, bind, pure, resolved,
    Option.isNone_none, Option.isSome_none, Option.map_none, Bool.false_eq_true, Option.orElse_eq_orElse, Option.orElse] at executed
  cases created : newDestination config.layout environment.act (.varr (.int .u8)) .value origin none (some bytes.length) before <;>
    simp [created, buildExpr, timeout, EvalM.stop] at executed

theorem execStmt_acceptedByteOwner_outcome (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context id : Nat) (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId)
    (rest : List Stmt) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (position : SourcePosition accepted frame (.statements (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin :: rest)))
    (nesting : frame.typingFuel = checkFuel + 1)
    (byteOwner : (frame.typing.variables[id]?).map (·.ty) = some (.varr (.int .u8)))
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none) :
    match execStmt fuel config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before with
    | .stop _ after => ∃ nextRegions, AcceptedWorld config frame.initialized after ambient types live nextRegions pending ∧
        AcceptedFrame config accepted frame after types
    | .ok flow after => flow = .normal .unit ∧ ∃ (scopeInst : Nat) (stored : StoredValue) (published : ExecutionState),
        let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
        let next := advanceLocalFrame { frame with typingFuel := checkFuel } id
        RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
        AcceptedWorld config frame.initialized after ambient (registerRootType types root (.varr (.int .u8)))
          (fun other => other = root ∨ live other)
          (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending ∧
        AcceptedFrame config accepted next after (registerRootType types root (.varr (.int .u8))) ∧
        SourcePosition accepted next (.statements rest)
    | .escape .. | .jump .. => False := by
  let statement := Stmt.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin
  have headPosition := position.statements_head accepted frame statement rest checkFuel nesting
  obtain ⟨typingNext, typingAfter, rootsAfter, typed, rooted⟩ := headPosition.checked accepted _ _
  cases checkFuel with
  | zero => change Except.error _ = Except.ok _ at typed; cases typed
  | succ checkFuel =>
    obtain ⟨descriptor, declared, localScope, order⟩ := typeStatement_let_descriptor checkFuel frame.typing typingNext id
      (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin frame.typingCounter typingAfter typed
    have descriptorType : descriptor.ty = .varr (.int .u8) := by
      simpa only [declared, Option.map_some, Option.some.injEq] using byteOwner
    have runtimeDeclared : frame.interpretation.environment.vars[id]? = some descriptor := by
      rw [source.compatible.variables]; exact declared
    have originFact := source.compatible.origin
    unfold SourceOrigin at originFact
    rw [phase] at originFact
    obtain ⟨original, calls, contextFound, implementationFound, implementationId, restOrigin⟩ := originFact
    have implementation : config.module.impls[frame.interpretation.environment.implementation]? = some frame.source.impl := by
      rw [implementationId]; exact implementationFound
    cases scopes : frame.interpretation.environment.scopes with
    | nil =>
      cases fuel with
      | zero => simp only [execStmt, timeout, EvalM.stop]; exact ⟨regions, world, source⟩
      | succ fuel =>
        simp only [execStmt, runtimeDeclared, rootOf, scopes, List.find?_nil, fault, EvalM.stop, bind]
        exact ⟨regions, world, source⟩
    | cons scopeEntry outer =>
      obtain ⟨scope, scopeInst⟩ := scopeEntry
      have sourceScopes : frame.source.scopes = scope :: outer.map Prod.fst := by
        rw [source.compatible.scopes, scopes]; rfl
      have localScope' := localScope.trans (source.compatible.currentScope scope (outer.map Prod.fst) sourceScopes)
      let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
      have resolved : rootOf frame.interpretation.environment id before = .ok root before := by
        simp only [rootOf, runtimeDeclared, scopes, List.find?_cons, localScope', beq_self_eq_true, pure, root]
      cases execution : execStmt fuel config frame.interpretation.environment statement before with
      | stop stop after =>
        exact execStmt_acceptedByteOwner_stopped_world fuel checkFuel config accepted frame context id scope scopeInst outer
          bytes origin bytesOrigin before after stop ambient types live regions pending typingNext typingAfter world source phase typed
          byteOwner scopes unnamed execution
      | ok flow after =>
        cases fuel with
        | zero => simp [statement, execStmt, timeout, EvalM.stop] at execution
        | succ fuel =>
          cases fuel with
          | zero => exact (byteStatement_one_not_ok config frame.interpretation.environment id descriptor frame.source.impl root
              bytes origin bytesOrigin before after flow runtimeDeclared descriptorType implementation unnamed resolved execution).elim
          | succ fuel =>
            have normal := execStmt_acceptedByteOwner_flow fuel (checkFuel + 1) config accepted frame context id bytes origin bytesOrigin rest
              before after flow types source phase position nesting byteOwner unnamed execution
            subst flow
            exact ⟨rfl, execStmt_byteOwner_statementsTail fuel (checkFuel + 1) config accepted frame context id bytes origin bytesOrigin rest
              before after ambient types live regions pending world source phase position nesting byteOwner unnamed execution⟩
      | escape target carriers after =>
        cases fuel with
        | zero => simp [statement, execStmt, timeout, EvalM.stop] at execution
        | succ fuel =>
          cases fuel with
          | zero =>
            simp only [statement, execStmt, runtimeDeclared, descriptorType, Ty.nonfixed, implementation, unnamed,
              ordinaryProducerCount?, producerCount?, literalCount, Option.isSome_some, ↓reduceIte, materializeProducer,
              bind, pure, resolved, Option.isNone_none, Option.isSome_none, Option.map_none, Bool.false_eq_true,
              Option.orElse_eq_orElse, Option.orElse] at execution
            cases created : newDestination config.layout frame.interpretation.environment.act (.varr (.int .u8)) .value origin none
                (some bytes.length) before with
            | ok value state => simp [created, buildExpr, timeout, EvalM.stop] at execution
            | stop reason state => simp [created] at execution
            | escape address values state =>
              have localAction := newByteDestination_local config frame.interpretation.environment origin bytes.length before
              rw [created] at localAction
              cases localAction
            | jump address kind state =>
              have localAction := newByteDestination_local config frame.interpretation.environment origin bytes.length before
              rw [created] at localAction
              cases localAction
          | succ fuel =>
            have localAction := execStmt_acceptedByteOwner_local fuel config accepted frame context id bytes origin bytesOrigin before types
              source phase byteOwner unnamed before
            rw [execution] at localAction
            exact localAction
      | jump target kind after =>
        cases fuel with
        | zero => simp [statement, execStmt, timeout, EvalM.stop] at execution
        | succ fuel =>
          cases fuel with
          | zero =>
            simp only [statement, execStmt, runtimeDeclared, descriptorType, Ty.nonfixed, implementation, unnamed,
              ordinaryProducerCount?, producerCount?, literalCount, Option.isSome_some, ↓reduceIte, materializeProducer,
              bind, pure, resolved, Option.isNone_none, Option.isSome_none, Option.map_none, Bool.false_eq_true,
              Option.orElse_eq_orElse, Option.orElse] at execution
            cases created : newDestination config.layout frame.interpretation.environment.act (.varr (.int .u8)) .value origin none
                (some bytes.length) before with
            | ok value state => simp [created, buildExpr, timeout, EvalM.stop] at execution
            | stop reason state => simp [created] at execution
            | escape address values state =>
              have localAction := newByteDestination_local config frame.interpretation.environment origin bytes.length before
              rw [created] at localAction
              cases localAction
            | jump address kind state =>
              have localAction := newByteDestination_local config frame.interpretation.environment origin bytes.length before
              rw [created] at localAction
              cases localAction
          | succ fuel =>
            have localAction := execStmt_acceptedByteOwner_local fuel config accepted frame context id bytes origin bytesOrigin before types
              source phase byteOwner unnamed before
            rw [execution] at localAction
            exact localAction

#print axioms execStmt_acceptedByteOwner_outcome

end Goose.Proofs.ConstructionAcceptedExecution

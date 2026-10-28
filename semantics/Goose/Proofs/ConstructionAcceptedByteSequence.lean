import Goose.Proofs.ConstructionAcceptedByteContinuation
import Goose.Proofs.ConstructionAcceptedPositions

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem SourcePosition.statements_tail {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (statement : Stmt) (rest : List Stmt) (fuel : Nat)
    (next : TypingEnv) (typingAfter : Nat) (rootsAfter : RState)
    (position : SourcePosition accepted frame (.statements (statement :: rest)))
    (nesting : frame.typingFuel = fuel + 1)
    (typedHead : typeStatement fuel frame.typing statement frame.typingCounter = .ok (next, typingAfter))
    (rootedHead : rpStmt frame.source statement frame.rootCursor = .ok ((), rootsAfter)) :
    SourcePosition accepted
      { frame with typingFuel := fuel, typing := next, typingCounter := typingAfter, rootCursor := rootsAfter }
      (.statements rest) := by
  obtain ⟨final, finalCounter, finalRoots, typed, rooted⟩ := position.checked accepted frame _
  obtain ⟨middle, first, remaining⟩ := rpStmts_cons rooted
  have same : middle = rootsAfter := by
    exact (Prod.mk.inj (Except.ok.inj (first.symm.trans rootedHead))).2
  subst middle
  rw [nesting] at typed
  simp only [typeStatements, bind, StateT.bind, typedHead, Except.bind] at typed
  exact .child position (.statementsTail frame statement rest fuel next typingAfter rootsAfter nesting typedHead rootedHead)
    ⟨final, finalCounter, finalRoots, typed, remaining⟩

theorem AcceptedFrame.withTypingFuel {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (fuel : Nat) :
    AcceptedFrame config accepted { frame with typingFuel := fuel } state types := by
  have compatible := source.compatible
  refine ⟨⟨compatible.module, compatible.rootModule, compatible.variables, compatible.sourceVariables,
    compatible.scopes, compatible.globalCount, compatible.globals, compatible.initialized, compatible.declarations,
    compatible.typingBound, compatible.visible, compatible.initializing, compatible.currentScope, ?_⟩,
    source.frontier, source.scopeFrontier, source.initializingBefore, source.aliases,
    source.locals, source.localTypes, source.uninitializedLocals, source.uninitializedTypes, source.futureGlobals,
    source.direct, source.contents⟩
  exact compatible.origin

theorem execStmt_byteOwner_statementsTail (runFuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context id : Nat) (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId)
    (rest : List Stmt) (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (position : SourcePosition accepted frame (.statements (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin :: rest)))
    (nesting : frame.typingFuel = checkFuel + 1)
    (byteOwner : (frame.typing.variables[id]?).map (·.ty) = some (.varr (.int .u8)))
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none)
    (executed : execStmt (runFuel + 2) config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .ok (.normal .unit) after) :
    ∃ (scopeInst : Nat) (stored : StoredValue) (published : ExecutionState),
      let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
      let next := advanceLocalFrame { frame with typingFuel := checkFuel } id
      RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
      AcceptedWorld config frame.initialized after ambient (registerRootType types root (.varr (.int .u8)))
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending ∧
      AcceptedFrame config accepted next after (registerRootType types root (.varr (.int .u8))) ∧
      SourcePosition accepted next (.statements rest) := by
  let statement := Stmt.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin
  let head := { frame with typingFuel := checkFuel }
  have headPosition : SourcePosition accepted head (.statement statement) :=
    position.statements_head accepted frame statement rest checkFuel nesting
  obtain ⟨typingNext, typingAfter, rootsAfter, typed, rooted⟩ := headPosition.checked accepted head _
  obtain ⟨scopeInst, stored, published, rootEq, typingEq, counterEq, extended, finalWorld, finalSource⟩ :=
    execStmt_byteOwner_continuation runFuel config accepted head context id bytes origin bytesOrigin before after ambient types
      live regions pending rootsAfter typingNext typingAfter world (source.withTypingFuel checkFuel) phase rooted typed byteOwner unnamed executed
  have tail := position.statements_tail accepted frame statement rest checkFuel typingNext typingAfter rootsAfter
    nesting typed rooted
  rw [rootEq, typingEq, counterEq] at tail
  refine ⟨scopeInst, stored, published, extended, finalWorld, finalSource, ?_⟩
  simpa only [head, advanceLocalFrame] using tail

#print axioms SourcePosition.statements_tail
#print axioms AcceptedFrame.withTypingFuel
#print axioms execStmt_byteOwner_statementsTail

end Goose.Proofs.ConstructionAcceptedExecution

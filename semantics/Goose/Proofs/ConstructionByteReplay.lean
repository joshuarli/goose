import Goose.Proofs.ConstructionAcceptedByteBatch

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

theorem execStmt_byteOwner_replay (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context : Nat) (declaration : ByteOwnerDeclaration) (rest : List Stmt)
    (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (position : SourcePosition accepted frame (.statements (declaration.statement :: rest)))
    (nesting : frame.typingFuel = checkFuel + 1)
    (owner : (frame.typing.variables[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none)
    (executed : execStmt (fuel + 2) config frame.interpretation.environment declaration.statement before = .ok (.normal .unit) after) :
    let next := advanceLocalFrame { frame with typingFuel := checkFuel } declaration.id
    typeStatement checkFuel frame.typing declaration.statement frame.typingCounter = .ok (next.typing, next.typingCounter) ∧
    rpStmt frame.source declaration.statement frame.rootCursor = .ok ((), next.rootCursor) := by
  let head := { frame with typingFuel := checkFuel }
  have headPosition := position.statements_head accepted frame declaration.statement rest checkFuel nesting
  obtain ⟨next, typingAfter, rootsAfter, typed, rooted⟩ := headPosition.checked accepted head _
  obtain ⟨scopeInst, stored, published, rootEq, typingEq, counterEq, extended, finalWorld, finalSource⟩ :=
    execStmt_byteOwner_continuation fuel config accepted head context declaration.id declaration.bytes declaration.origin
      declaration.bytesOrigin before after ambient types live regions pending rootsAfter next typingAfter world
      (source.withTypingFuel checkFuel) phase (by simpa only [ByteOwnerDeclaration.statement] using rooted)
      (by simpa only [ByteOwnerDeclaration.statement] using typed) owner unnamed
      (by simpa only [ByteOwnerDeclaration.statement] using executed)
  rw [typingEq, counterEq] at typed
  rw [rootEq] at rooted
  exact ⟨typed, rooted⟩

theorem statementReplay_cons (fuel : Nat) (frame next final : ConstructionSourceFrame)
    (statement : Stmt) (rest : List Stmt)
    (typing : typeStatement fuel frame.typing statement frame.typingCounter = .ok (next.typing, next.typingCounter))
    (rooting : rpStmt frame.source statement frame.rootCursor = .ok ((), next.rootCursor))
    (source : next.source = frame.source)
    (tailTyping : typeStatements fuel next.typing rest next.typingCounter = .ok (final.typing, final.typingCounter))
    (tailRooting : rpStmts next.source rest next.rootCursor = .ok ((), final.rootCursor)) :
    typeStatements (fuel + 1) frame.typing (statement :: rest) frame.typingCounter = .ok (final.typing, final.typingCounter) ∧
    rpStmts frame.source (statement :: rest) frame.rootCursor = .ok ((), final.rootCursor) := by
  constructor
  · simp only [typeStatements, bind, StateT.bind, typing, Except.bind, tailTyping]
  · simp only [rpStmts, bind, StateT.bind, rooting, Except.bind]
    simpa only [source] using tailRooting

#print axioms statementReplay_cons
#print axioms execStmt_byteOwner_replay
end Goose.Proofs.ConstructionAcceptedExecution

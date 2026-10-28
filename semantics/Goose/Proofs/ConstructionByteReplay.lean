import Goose.Proofs.ConstructionAcceptedByteBatch
import Goose.Proofs.ConstructionByteStatementOutcome

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

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

theorem execStmts_byteOwners_normalTail_replay (declarations : List ByteOwnerDeclaration) :
    ∀ (runFuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
      (frame : ConstructionSourceFrame) (context : Nat) (rest : List Stmt)
      (before after : ExecutionState) (result : Value) (ambient : OwnershipAmbient) (types : RootTypes)
      (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame),
      declarations.length + 2 ≤ runFuel → declarations.length ≤ checkFuel → frame.typingFuel = checkFuel + 1 →
      AcceptedWorld config frame.initialized before ambient types live regions pending →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation context →
      SourcePosition accepted frame (.statements (declarations.map ByteOwnerDeclaration.statement ++ rest)) →
      (∀ declaration ∈ declarations, (frame.typing.variables[declaration.id]?).map (·.ty) = some (.varr (.int .u8))) →
      (∀ declaration ∈ declarations,
        (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none) →
      execStmts runFuel config frame.interpretation.environment (declarations.map ByteOwnerDeclaration.statement ++ rest)
        before = .ok (.normal result) after →
      ∃ (remainingFuel : Nat) (next : ConstructionSourceFrame) (middle : ExecutionState)
        (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (nextRegions : List ReceivingRegion),
        remainingFuel + declarations.length = runFuel ∧
        next.interpretation = frame.interpretation ∧ next.initialized = frame.initialized ∧ next.source = frame.source ∧ next.phase = frame.phase ∧
        typeStatements frame.typingFuel frame.typing (declarations.map ByteOwnerDeclaration.statement) frame.typingCounter =
          .ok (next.typing, next.typingCounter) ∧
        rpStmts frame.source (declarations.map ByteOwnerDeclaration.statement) frame.rootCursor = .ok ((), next.rootCursor) ∧
        execStmts remainingFuel config next.interpretation.environment rest middle = .ok (.normal result) after ∧
        RootTypesExtend types nextTypes ∧
        AcceptedWorld config next.initialized middle ambient nextTypes nextLive nextRegions pending ∧
        AcceptedFrame config accepted next middle nextTypes ∧ SourcePosition accepted next (.statements rest) := by
  intro runFuel checkFuel config accepted frame context rest before after result ambient types live regions pending
  induction declarations generalizing runFuel checkFuel frame before types live regions with
  | nil =>
    intro enoughRun enoughCheck nesting world source phase position owners unnamed executed
    have typed : typeStatements frame.typingFuel frame.typing [] frame.typingCounter = .ok (frame.typing, frame.typingCounter) := by
      rw [nesting]
      simp [typeStatements, pure, StateT.pure, Except.pure]
    exact ⟨runFuel, frame, before, types, live, regions, by simp, rfl, rfl, rfl, rfl, typed, rfl, executed,
      (fun root ty found => found), world, source, position⟩
  | cons declaration declarations ih =>
    intro enoughRun enoughCheck nesting world source phase position owners unnamed executed
    cases runFuel with
    | zero => simp at enoughRun
    | succ runFuel =>
     cases runFuel with
     | zero => simp at enoughRun
     | succ runFuel =>
      cases runFuel with
      | zero => simp at enoughRun
      | succ runFuel =>
       cases checkFuel with
       | zero => simp at enoughCheck
       | succ checkFuel =>
        have headOwner := owners declaration (by simp)
        have headUnnamed := unnamed declaration (by simp)
        have headPosition : SourcePosition accepted frame (.statements
            (declaration.statement :: (declarations.map ByteOwnerDeclaration.statement ++ rest))) := by
          simpa only [List.map_cons, List.cons_append] using position
        have headExecuted : execStmts (runFuel + 3) config frame.interpretation.environment
            (declaration.statement :: (declarations.map ByteOwnerDeclaration.statement ++ rest)) before = .ok (.normal result) after := by
          simpa only [List.map_cons, List.cons_append] using executed
        obtain ⟨headValue, headMiddle, headExecution, _⟩ := execStmts_normal_head (runFuel + 2) config
          frame.interpretation.environment declaration.statement (declarations.map ByteOwnerDeclaration.statement ++ rest)
          before after result headExecuted
        have headOutcome := execStmt_acceptedByteOwner_flow runFuel (checkFuel + 1) config accepted frame context declaration.id
          declaration.bytes declaration.origin declaration.bytesOrigin (declarations.map ByteOwnerDeclaration.statement ++ rest)
          before headMiddle (.normal headValue) types source phase headPosition nesting headOwner headUnnamed (by
            simpa only [ByteOwnerDeclaration.statement] using headExecution)
        have unit : headValue = .unit := by cases headOutcome; rfl
        subst headValue
        have headReplay := execStmt_byteOwner_replay runFuel (checkFuel + 1) config accepted frame context declaration
          (declarations.map ByteOwnerDeclaration.statement ++ rest) before headMiddle ambient types live regions pending
          world source phase headPosition nesting headOwner headUnnamed headExecution
        obtain ⟨middle, scopeInst, stored, published, tail, extended, middleWorld, middleSource, middlePosition⟩ :=
          execStmts_byteOwner_normalTail runFuel (checkFuel + 1) config accepted frame context declaration.id declaration.bytes
            declaration.origin declaration.bytesOrigin (declarations.map ByteOwnerDeclaration.statement ++ rest)
            before after result ambient types live regions pending world source phase headPosition (by omega) headOwner headUnnamed headExecuted
        let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst declaration.id
        let nextTypes := registerRootType types root (.varr (.int .u8))
        let nextFrame := advanceLocalFrame { frame with typingFuel := checkFuel + 1 } declaration.id
        let nextLive := fun other => other = root ∨ live other
        let nextRegions := regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))
        have remainingOwners : ∀ item ∈ declarations, (nextFrame.typing.variables[item.id]?).map (·.ty) = some (.varr (.int .u8)) := by
          intro item member
          exact owners item (List.mem_cons_of_mem declaration member)
        have remainingUnnamed : ∀ item ∈ declarations,
            (nextFrame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some item.id)) = none := by
          intro item member
          exact unnamed item (List.mem_cons_of_mem declaration member)
        obtain ⟨remainingFuel, finalFrame, finalState, finalTypes, finalLive, finalRegions,
          fuelEq, interpretationEq, initializedEq, sourceEq, phaseEq, tailTyped, tailRooted, finalTail, typesExtended, finalWorld, finalSource, finalPosition⟩ :=
          ih (runFuel + 2) checkFuel nextFrame middle nextTypes nextLive nextRegions
            (by simp only [List.length_cons] at enoughRun; omega) (by simp only [List.length_cons] at enoughCheck; omega) rfl
            middleWorld middleSource (by simpa only [nextFrame, advanceLocalFrame] using phase) middlePosition remainingOwners remainingUnnamed tail
        have replay := statementReplay_cons (checkFuel + 1) frame nextFrame finalFrame declaration.statement
          (declarations.map ByteOwnerDeclaration.statement) headReplay.1 headReplay.2 rfl tailTyped tailRooted
        refine ⟨remainingFuel, finalFrame, finalState, finalTypes, finalLive, finalRegions, ?_, ?_, ?_, ?_, ?_, ?_, ?_, finalTail, ?_, finalWorld, finalSource, finalPosition⟩
        · simp only [List.length_cons] at *; omega
        · exact interpretationEq
        · exact initializedEq
        · exact sourceEq
        · exact phaseEq
        · simpa only [nesting, List.map_cons] using replay.1
        · simpa only [List.map_cons] using replay.2
        · intro oldRoot ty found
          exact typesExtended oldRoot ty (extended oldRoot ty found)

#print axioms execStmts_byteOwners_normalTail_replay
#print axioms statementReplay_cons
#print axioms execStmt_byteOwner_replay
end Goose.Proofs.ConstructionAcceptedExecution

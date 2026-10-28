import Goose.Proofs.ConstructionByteStatementOutcome
import Goose.Proofs.ConstructionAcceptedByteBatch

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem execStmts_byteOwners_accepted_world (declarations : List ByteOwnerDeclaration) :
    ∀ (runFuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
      (frame : ConstructionSourceFrame) (context : Nat) (before : ExecutionState)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
      (regions : List ReceivingRegion) (pending : List PendingCarrierFrame),
      declarations.length ≤ checkFuel → frame.typingFuel = checkFuel + 1 →
      AcceptedWorld config frame.initialized before ambient types live regions pending →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation context →
      SourcePosition accepted frame (.statements (declarations.map ByteOwnerDeclaration.statement)) →
      (∀ declaration ∈ declarations, (frame.typing.variables[declaration.id]?).map (·.ty) = some (.varr (.int .u8))) →
      (∀ declaration ∈ declarations,
        (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none) →
      ∃ (next : ConstructionSourceFrame) (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop)
        (nextRegions : List ReceivingRegion),
        let outcome := execStmts runFuel config frame.interpretation.environment (declarations.map ByteOwnerDeclaration.statement) before
        let after := Goose.Proofs.Exit.stepState outcome
        next.initialized = frame.initialized ∧ RootTypesExtend types nextTypes ∧
        AcceptedWorld config next.initialized after ambient nextTypes nextLive nextRegions pending ∧
        AcceptedFrame config accepted next after nextTypes ∧
        (match outcome with | .ok flow _ => flow = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) := by
  intro runFuel checkFuel config accepted frame context before ambient types live regions pending
  induction declarations generalizing runFuel checkFuel frame before types live regions with
  | nil =>
    intro enough nesting world source phase position owners unnamed
    cases runFuel with
    | zero =>
      simp only [List.map_nil, execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), world, source, trivial⟩
    | succ fuel =>
      simp only [List.map_nil, execStmts, pure, Goose.Proofs.Exit.stepState]
      exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), world, source, trivial⟩
  | cons declaration declarations ih =>
    intro enough nesting world source phase position owners unnamed
    cases checkFuel with
    | zero => simp at enough
    | succ checkFuel =>
      have headOwner := owners declaration (by simp)
      have headUnnamed := unnamed declaration (by simp)
      have headPosition : SourcePosition accepted frame (.statements
          (declaration.statement :: declarations.map ByteOwnerDeclaration.statement)) := by
        simpa only [List.map_cons, ByteOwnerDeclaration.statement] using position
      cases runFuel with
      | zero =>
        simp only [List.map_cons, execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
        exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), world, source, trivial⟩
      | succ runFuel =>
        have headOutcome := execStmt_acceptedByteOwner_outcome runFuel (checkFuel + 1) config accepted frame context declaration.id
          declaration.bytes declaration.origin declaration.bytesOrigin (declarations.map ByteOwnerDeclaration.statement) before ambient types
          live regions pending world source phase headPosition (by omega) headOwner headUnnamed
        cases head : execStmt runFuel config frame.interpretation.environment declaration.statement before with
        | stop reason after =>
          have head' := head
          simp only [ByteOwnerDeclaration.statement] at head'
          simp only [head'] at headOutcome
          obtain ⟨nextRegions, finalWorld, finalSource⟩ := headOutcome
          simp only [List.map_cons, execStmts, bind, head, Goose.Proofs.Exit.stepState]
          exact ⟨frame, types, live, nextRegions, rfl, (fun _ _ found => found), finalWorld, finalSource, trivial⟩
        | escape address carriers after =>
          have head' := head
          simp only [ByteOwnerDeclaration.statement] at head'
          simp only [head'] at headOutcome
        | jump target kind after =>
          have head' := head
          simp only [ByteOwnerDeclaration.statement] at head'
          simp only [head'] at headOutcome
        | ok flow middle =>
          have head' := head
          simp only [ByteOwnerDeclaration.statement] at head'
          simp only [head'] at headOutcome
          obtain ⟨normal, scopeInst, stored, published, extended, middleWorld, middleSource, middlePosition⟩ := headOutcome
          subst flow
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
          obtain ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, finalExtended, finalWorld, finalSource, finalFlow⟩ :=
            ih runFuel checkFuel nextFrame middle nextTypes nextLive nextRegions
              (by simp only [List.length_cons] at enough; omega) rfl middleWorld middleSource
              (by simpa only [nextFrame, advanceLocalFrame] using phase) middlePosition remainingOwners remainingUnnamed
          simp only [List.map_cons, execStmts, bind, head]
          refine ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, ?_, finalWorld, finalSource, finalFlow⟩
          intro oldRoot ty found
          exact finalExtended oldRoot ty (extended oldRoot ty found)

#print axioms execStmts_byteOwners_accepted_world

end Goose.Proofs.ConstructionAcceptedExecution

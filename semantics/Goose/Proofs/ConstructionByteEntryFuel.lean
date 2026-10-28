import Goose.Proofs.ConstructionByteStatementOutcome
import Goose.Proofs.ConstructionAcceptedByteBatch
import Goose.Proofs.ConstructionAcceptedByteTimeout

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem execStmts_byteOwners_normalFuel (declarations : List ByteOwnerDeclaration) :
    ∀ (runFuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
      (frame : ConstructionSourceFrame) (context : Nat) (before after : ExecutionState)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
      (regions : List ReceivingRegion) (pending : List PendingCarrierFrame),
      declarations.length ≤ checkFuel → frame.typingFuel = checkFuel + 1 →
      AcceptedWorld config frame.initialized before ambient types live regions pending →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation context →
      SourcePosition accepted frame (.statements (declarations.map ByteOwnerDeclaration.statement)) →
      (∀ declaration ∈ declarations, (frame.typing.variables[declaration.id]?).map (·.ty) = some (.varr (.int .u8))) →
      (∀ declaration ∈ declarations,
        (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none) →
      execStmts runFuel config frame.interpretation.environment (declarations.map ByteOwnerDeclaration.statement) before = .ok (.normal .unit) after →
      declarations.length + 1 ≤ runFuel ∧ (declarations ≠ [] → declarations.length + 2 ≤ runFuel) := by
  intro runFuel checkFuel config accepted frame context before after ambient types live regions pending
  induction declarations generalizing runFuel checkFuel frame before types live regions with
  | nil =>
    intro enough nesting world source phase position owners unnamed executed
    cases runFuel with
    | zero => simp [execStmts, timeout, EvalM.stop] at executed
    | succ fuel => simp
  | cons declaration declarations ih =>
    intro enough nesting world source phase position owners unnamed executed
    cases checkFuel with
    | zero => simp at enough
    | succ checkFuel =>
      have headPosition : SourcePosition accepted frame (.statements (declaration.statement :: declarations.map ByteOwnerDeclaration.statement)) := by
        simpa only [List.map_cons] using position
      have headOwner := owners declaration (by simp)
      have headUnnamed := unnamed declaration (by simp)
      cases runFuel with
      | zero => simp [execStmts, timeout, EvalM.stop] at executed
      | succ runFuel =>
        cases runFuel with
        | zero => simp [execStmts, execStmt, timeout, EvalM.stop, bind] at executed
        | succ runFuel =>
          have headExecuted : execStmts (runFuel + 2) config frame.interpretation.environment
              (declaration.statement :: declarations.map ByteOwnerDeclaration.statement) before = .ok (.normal .unit) after := by
            simpa only [List.map_cons] using executed
          obtain ⟨value, middle, head, tail⟩ := execStmts_normal_head (runFuel + 1) config frame.interpretation.environment
            declaration.statement (declarations.map ByteOwnerDeclaration.statement) before after .unit headExecuted
          cases runFuel with
          | zero =>
            have headPosition' := headPosition.statements_head accepted frame declaration.statement
              (declarations.map ByteOwnerDeclaration.statement) (checkFuel + 1) nesting
            obtain ⟨typingNext, typingAfter, rootsAfter, typed, rooted⟩ := headPosition'.checked accepted _ _
            exact (execStmt_acceptedByteOwner_one_ne_ok config accepted { frame with typingFuel := checkFuel + 1 }
              context declaration.id declaration.bytes declaration.origin declaration.bytesOrigin before middle (.normal value) types
              typingNext typingAfter (source.withTypingFuel (checkFuel + 1)) phase (by simpa [ByteOwnerDeclaration.statement] using typed)
              headOwner headUnnamed (by simpa [ByteOwnerDeclaration.statement] using head)).elim
          | succ runFuel =>
            have headOutcome := execStmt_acceptedByteOwner_outcome (runFuel + 2) (checkFuel + 1) config accepted frame context
              declaration.id declaration.bytes declaration.origin declaration.bytesOrigin (declarations.map ByteOwnerDeclaration.statement)
              before ambient types live regions pending world source phase headPosition nesting headOwner headUnnamed
            have head' := head
            simp only [ByteOwnerDeclaration.statement] at head'
            simp only [head'] at headOutcome
            obtain ⟨same, scopeInst, stored, published, extended, middleWorld, middleSource, middlePosition⟩ := headOutcome
            cases same
            let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst declaration.id
            let nextTypes := registerRootType types root (.varr (.int .u8))
            let nextFrame := advanceLocalFrame { frame with typingFuel := checkFuel + 1 } declaration.id
            let nextLive := fun other => other = root ∨ live other
            let nextRegions := regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))
            have remainingOwners : ∀ item ∈ declarations, (nextFrame.typing.variables[item.id]?).map (·.ty) = some (.varr (.int .u8)) := by
              intro item member; exact owners item (List.mem_cons_of_mem declaration member)
            have remainingUnnamed : ∀ item ∈ declarations,
                (nextFrame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some item.id)) = none := by
              intro item member; exact unnamed item (List.mem_cons_of_mem declaration member)
            obtain ⟨tailBound, tailNonemptyBound⟩ := ih (runFuel + 2) checkFuel nextFrame middle nextTypes nextLive nextRegions
              (by simp only [List.length_cons] at enough; omega) rfl middleWorld middleSource
              (by simpa only [nextFrame, advanceLocalFrame] using phase) middlePosition remainingOwners remainingUnnamed tail
            have full : (declaration :: declarations).length + 2 ≤ runFuel + 3 := by
              cases declarations with
              | nil => simp
              | cons first rest => have bound := tailNonemptyBound (by simp); simp only [List.length_cons] at *; omega
            exact ⟨by simp only [List.length_cons] at *; omega, fun _ => full⟩

#print axioms execStmts_byteOwners_normalFuel
end Goose.Proofs.ConstructionAcceptedExecution

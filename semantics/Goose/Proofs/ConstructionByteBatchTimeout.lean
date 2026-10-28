import Goose.Proofs.ConstructionByteSequenceTimeout
import Goose.Proofs.ConstructionAcceptedBytePrefix

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execStmts_byteOwners_timeout_tail (declarations : List ByteOwnerDeclaration)
    (runFuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context : Nat) (rest : List Stmt)
    (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (enoughRun : declarations.length + 2 ≤ runFuel) (enoughCheck : declarations.length ≤ checkFuel)
    (nesting : frame.typingFuel = checkFuel + 1)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (position : SourcePosition accepted frame (.statements (declarations.map ByteOwnerDeclaration.statement ++ rest)))
    (owners : ∀ declaration ∈ declarations, (frame.typing.variables[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (unnamed : ∀ declaration ∈ declarations,
      (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none)
    (executed : execStmts runFuel config frame.interpretation.environment (declarations.map ByteOwnerDeclaration.statement ++ rest)
      before = .stop .timeout after) :
    ∃ (remainingFuel : Nat) (next : ConstructionSourceFrame) (middle : ExecutionState)
      (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (nextRegions : List ReceivingRegion),
      remainingFuel + declarations.length = runFuel ∧ next.interpretation = frame.interpretation ∧
      next.initialized = frame.initialized ∧ execStmts remainingFuel config next.interpretation.environment rest middle = .stop .timeout after ∧
      RootTypesExtend types nextTypes ∧ AcceptedWorld config next.initialized middle ambient nextTypes nextLive nextRegions pending ∧
      AcceptedFrame config accepted next middle nextTypes ∧ SourcePosition accepted next (.statements rest) := by
  obtain ⟨completed, remaining, remainingFuel, next, middle, nextTypes, nextLive, nextRegions,
    decomposition, fuelEq, interpretationEq, initializedEq, phaseEq, variablesEq, sourceEq, extended,
    nextWorld, nextSource, nextPosition, outcome⟩ :=
    execStmts_byteOwners_prefix declarations runFuel checkFuel config accepted frame context rest before (.stop .timeout after)
      ambient types live regions pending enoughRun enoughCheck nesting world source phase position owners unnamed executed
  rcases outcome with ⟨rfl, tail⟩ | ⟨declaration, remainingTail, remainingEq, stopped⟩
  · have completedEq : completed = declarations := by simpa using decomposition.symm
    subst completed
    exact ⟨remainingFuel, next, middle, nextTypes, nextLive, nextRegions, fuelEq, interpretationEq, initializedEq,
      tail, extended, nextWorld, nextSource, by simpa using nextPosition⟩
  · have member : declaration ∈ declarations := by rw [decomposition, remainingEq]; simp
    have enough : 2 ≤ remainingFuel - 1 := by
      have lengthEq := congrArg List.length decomposition
      simp only [List.length_append, remainingEq, List.length_cons] at lengthEq
      omega
    obtain ⟨headFuel, fuelShape⟩ := Nat.exists_eq_add_of_le enough
    have headOwner : (next.typing.variables[declaration.id]?).map (·.ty) = some (.varr (.int .u8)) := by
      rw [variablesEq]
      exact owners declaration member
    have headUnnamed : (next.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none := by
      rw [sourceEq]
      exact unnamed declaration member
    have headPhase : next.phase = .implementation context := phaseEq.trans phase
    have noTimeout := execStmt_acceptedByteOwner_local headFuel config accepted next context declaration.id declaration.bytes
      declaration.origin declaration.bytesOrigin middle nextTypes nextSource headPhase headOwner headUnnamed middle
    have headStopped : execStmt (headFuel + 2) config next.interpretation.environment declaration.statement middle = .stop .timeout after := by
      simpa only [fuelShape, ByteOwnerDeclaration.statement, Nat.add_comm] using stopped
    have headStopped' : execStmt (headFuel + 2) config next.interpretation.environment
        (.letS declaration.id (.bytes (.varr (.int .u8)) declaration.bytes declaration.bytesOrigin) declaration.origin)
        middle = .stop .timeout after := by simpa only [ByteOwnerDeclaration.statement] using headStopped
    rw [headStopped'] at noTimeout
    exact (noTimeout rfl).elim

#print axioms execStmts_byteOwners_timeout_tail

end Goose.Proofs.ConstructionAcceptedExecution

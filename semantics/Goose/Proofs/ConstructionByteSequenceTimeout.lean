import Goose.Proofs.ConstructionByteNoTimeout
import Goose.Proofs.ConstructionAcceptedByteAbnormalSequence

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execStmts_acceptedByteOwner_timeout_split (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context id : Nat) (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId)
    (rest : List Stmt) (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (position : SourcePosition accepted frame (.statements (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin :: rest)))
    (nesting : frame.typingFuel = checkFuel + 1)
    (byteOwner : (frame.typing.variables[id]?).map (·.ty) = some (.varr (.int .u8)))
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none)
    (executed : execStmts fuel config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin :: rest) before = .stop .timeout after) :
    (after = before ∧ AcceptedWorld config frame.initialized after ambient types live regions pending ∧
      AcceptedFrame config accepted frame after types) ∨
    (∃ destination, AcceptedWorld config frame.initialized after ambient types live
      (freshReceivingRegion before destination :: regions) pending ∧ AcceptedFrame config accepted frame after types) ∨
    ∃ (middle : ExecutionState) (scopeInst : Nat) (stored : StoredValue) (published : ExecutionState) (tailFuel : Nat),
      let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
      let next := advanceLocalFrame { frame with typingFuel := checkFuel } id
      execStmts tailFuel config frame.interpretation.environment rest middle = .stop .timeout after ∧
      RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
      AcceptedWorld config frame.initialized middle ambient (registerRootType types root (.varr (.int .u8)))
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending ∧
      AcceptedFrame config accepted next middle (registerRootType types root (.varr (.int .u8))) ∧
      SourcePosition accepted next (.statements rest) := by
  cases fuel with
  | zero =>
    simp only [execStmts, timeout, EvalM.stop, ExecutionStep.stop.injEq, true_and] at executed
    subst after
    exact Or.inl ⟨rfl, world, source⟩
  | succ fuel =>
    cases fuel with
    | zero =>
      simp only [execStmts, execStmt, timeout, EvalM.stop, bind, ExecutionStep.stop.injEq, true_and] at executed
      subst after
      exact Or.inl ⟨rfl, world, source⟩
    | succ fuel =>
      cases fuel with
      | zero =>
        exact Or.inr (Or.inl (execStmts_acceptedByteOwner_timeout_world checkFuel config accepted frame context id bytes origin bytesOrigin
          rest before after ambient types live regions pending world source phase position nesting byteOwner unnamed executed))
      | succ fuel =>
        have split := execStmts_byteOwner_split fuel checkFuel config accepted frame context id bytes origin bytesOrigin rest before
          (.stop .timeout after) ambient types live regions pending world source phase position nesting byteOwner unnamed executed
        rcases split with stopped | ⟨middle, scopeInst, stored, published, tail, extended, nextWorld, nextFrame, nextPosition⟩
        · have noTimeout := execStmt_acceptedByteOwner_local fuel config accepted frame context id bytes origin bytesOrigin
            before types source phase byteOwner unnamed before
          rw [stopped] at noTimeout
          exact (noTimeout rfl).elim
        · exact Or.inr (Or.inr ⟨middle, scopeInst, stored, published, fuel + 2, tail, extended, nextWorld, nextFrame, nextPosition⟩)

#print axioms execStmts_acceptedByteOwner_timeout_split

end Goose.Proofs.ConstructionAcceptedExecution

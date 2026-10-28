import Goose.Proofs.ConstructionByteStatementStopped

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem execStmt_acceptedByteOwner_allScopes_stopped_world (fuel typeFuel : Nat) (config : EvalConfig)
    (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (context id : Nat)
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId)
    (before after : ExecutionState) (stop : Goose.Core.Stop) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (typingNext : TypingEnv) (typingAfter : Nat)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (typed : typeStatement (typeFuel + 1) frame.typing (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin)
      frame.typingCounter = .ok (typingNext, typingAfter))
    (byteOwner : (frame.typing.variables[id]?).map (·.ty) = some (.varr (.int .u8)))
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none)
    (executed : execStmt fuel config frame.interpretation.environment
      (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .stop stop after) :
    ∃ nextRegions, AcceptedWorld config frame.initialized after ambient types live nextRegions pending ∧
      AcceptedFrame config accepted frame after types := by
  cases scopes : frame.interpretation.environment.scopes with
  | nil =>
    cases fuel with
    | zero =>
      simp only [execStmt, timeout, EvalM.stop, ExecutionStep.stop.injEq] at executed
      obtain ⟨_, same⟩ := executed
      subst after
      exact ⟨regions, world, source⟩
    | succ fuel =>
      cases declared : frame.interpretation.environment.vars[id]? with
      | none =>
        simp only [execStmt, declared, fault, EvalM.stop, ExecutionStep.stop.injEq] at executed
        obtain ⟨_, same⟩ := executed
        subst after
        exact ⟨regions, world, source⟩
      | some descriptor =>
        simp only [execStmt, declared, rootOf, scopes, List.find?_nil, fault, EvalM.stop, bind,
          ExecutionStep.stop.injEq] at executed
        obtain ⟨_, same⟩ := executed
        subst after
        exact ⟨regions, world, source⟩
  | cons first outer =>
    obtain ⟨scope, scopeInst⟩ := first
    exact execStmt_acceptedByteOwner_stopped_world fuel typeFuel config accepted frame context id scope scopeInst outer bytes origin bytesOrigin
      before after stop ambient types live regions pending typingNext typingAfter world source phase typed byteOwner scopes unnamed executed

#print axioms execStmt_acceptedByteOwner_allScopes_stopped_world

end Goose.Proofs.ConstructionAcceptedExecution

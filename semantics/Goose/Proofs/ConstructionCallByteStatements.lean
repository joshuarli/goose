import Goose.Proofs.ConstructionAcceptedEmptyCallFrame
import Goose.Proofs.ConstructionByteEntryFrameComplete

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem callByteStatements_accepted_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (contextId : Nat) (activation : RuntimeActivation) (activated before : ExecutionState)
    (declarations : List ByteOwnerDeclaration) (ambient : OwnershipAmbient) (priorTypes : RootTypes)
    (live : Goose.Core.RootInst → Prop) (priorRegions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config (entryStatementsFrame config frame activated.nextScope).initialized before
      (.callChannels activation [] :: ambient) priorTypes live priorRegions pending)
    (source : AcceptedFrame config accepted (entryStatementsFrame config frame activated.nextScope) before
      priorTypes)
    (position : SourcePosition accepted (entryStatementsFrame config frame activated.nextScope)
      (.statements frame.source.impl.body.stmts))
    (phase : frame.phase = .implementation contextId) (results : frame.source.impl.results = #[])
    (body : frame.source.impl.body.stmts = declarations.map ByteOwnerDeclaration.statement)
    (owners : ∀ declaration ∈ declarations,
      (frame.source.impl.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (checkFuel : declarations.length ≤ 4094) :
    ∃ (next : ConstructionSourceFrame) (types : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion),
      let entryFrame := entryStatementsFrame config frame activated.nextScope
      let outcome := execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before
      let after := Goose.Proofs.Exit.stepState outcome
      next.initialized = entryFrame.initialized ∧ RootTypesExtend priorTypes types ∧
      AcceptedWorld config next.initialized after (.callChannels activation [] :: ambient) types nextLive regions pending ∧
      AcceptedFrame config accepted next after types ∧
      (match outcome with | .ok flow _ => flow = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) := by
  let entryFrame := entryStatementsFrame config frame activated.nextScope
  have position' : SourcePosition accepted entryFrame (.statements (declarations.map ByteOwnerDeclaration.statement)) := by
    rw [← body]
    exact position
  have owners' : ∀ declaration ∈ declarations,
      (entryFrame.typing.variables[declaration.id]?).map (·.ty) = some (.varr (.int .u8)) := by
    intro declaration member
    simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using owners declaration member
  have unnamed : ∀ declaration ∈ declarations,
      (entryFrame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none := by
    intro declaration member
    simp only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, results,
      Array.toList_empty, List.zipIdx_nil, List.find?_nil]
  obtain ⟨next, types, nextLive, regions, initializedEq, extended, finalWorld, finalSource, finalFlow⟩ :=
    execStmts_byteOwners_accepted_world declarations fuel 4094 config accepted entryFrame contextId before
      (.callChannels activation [] :: ambient) priorTypes live priorRegions pending checkFuel rfl
      world source (by simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using phase)
      position' owners' unnamed
  refine ⟨next, types, nextLive, regions, initializedEq, extended, ?_, ?_, ?_⟩
  · simpa only [← body] using finalWorld
  · simpa only [← body] using finalSource
  · rw [← body] at finalFlow
    cases outcome : execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before <;>
      simp only [outcome] at finalFlow ⊢ <;> exact finalFlow

#print axioms callByteStatements_accepted_world
end Goose.Proofs.ConstructionAcceptedExecution

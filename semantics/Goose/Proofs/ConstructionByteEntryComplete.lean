import Goose.Proofs.ConstructionByteBatchComplete
import Goose.Proofs.ConstructionAcceptedEntryInvocation

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedZeroGlobalEntryByteBody (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (declarations : List ByteOwnerDeclaration) (original : Context) (implementation : Impl)
    (noGlobals : config.module.globals.size = 0)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = declarations.map ByteOwnerDeclaration.statement)
    (owners : ∀ declaration ∈ declarations,
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (checkFuel : declarations.length ≤ 4094) :
    ∃ (frame next : ConstructionSourceFrame) (activation : RuntimeActivation)
      (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion),
      let initial := ExecutionState.initial
      let environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
      let activated := { initial with nextAct := initial.nextAct + 1, activations := activation :: initial.activations }
      let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let entryFrame := entryStatementsFrame config frame activated.nextScope
      let outcome := execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before
      let after := Goose.Proofs.Exit.stepState outcome
      runModule (fuel + 3) config initial =
        (invokeCall (fuel + 3) config environment config.module.entry [] [] 0 >>= fun carriers => publishCarriers 0 carriers) initial ∧
      invokeCall (fuel + 3) config environment config.module.entry [] [] 0 initial =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated ∧
      frame.source.impl = implementation ∧ next.initialized = entryFrame.initialized ∧
      RootTypesExtend (declaredRootTypes config.module) types ∧
      AcceptedWorld config next.initialized after [.callChannels activation []] types live regions [] ∧
      AcceptedFrame config accepted next after types ∧
      (match outcome with | .ok flow _ => flow = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) := by
  obtain ⟨frame, activation, moduleStep, callStep, environmentEq, world, source, position, phase, results⟩ :=
    acceptedZeroGlobalRunEntry fuel config accepted noGlobals
  let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1, activations := activation :: ExecutionState.initial.activations }
  let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
  let entryFrame := entryStatementsFrame config frame activated.nextScope
  have originFact := source.compatible.origin
  unfold SourceOrigin at originFact
  simp only [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame,
    RootInterpretation.enterScope, phase] at originFact
  obtain ⟨entry, calls, entryAt, implAt, originRest⟩ := originFact
  have entryEq : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
  subst entry
  have implementationEq : frame.source.impl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
  have position' : SourcePosition accepted entryFrame (.statements (declarations.map ByteOwnerDeclaration.statement)) := by
    rw [← body, ← implementationEq]
    exact position
  have owners' : ∀ declaration ∈ declarations,
      (entryFrame.typing.variables[declaration.id]?).map (·.ty) = some (.varr (.int .u8)) := by
    intro declaration member
    simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, implementationEq] using owners declaration member
  have unnamed : ∀ declaration ∈ declarations,
      (entryFrame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none := by
    intro declaration member
    simp only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, results,
      Array.toList_empty, List.zipIdx_nil, List.find?_nil]
  obtain ⟨next, types, live, regions, initializedEq, extended, finalWorld, finalSource, finalFlow⟩ :=
    execStmts_byteOwners_accepted_world declarations fuel 4094 config accepted entryFrame config.module.entry before
      [.callChannels activation []] (declaredRootTypes config.module) (fun _ => False) [] [] checkFuel rfl
      world source (by simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using phase)
      position' owners' unnamed
  refine ⟨frame, next, activation, types, live, regions, moduleStep, callStep, implementationEq, initializedEq, extended, ?_, ?_, ?_⟩
  · simpa only [← body, ← implementationEq] using finalWorld
  · simpa only [← body, ← implementationEq] using finalSource
  · rw [← body, ← implementationEq] at finalFlow
    cases evaluated : execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before <;>
      simp only [evaluated] at finalFlow ⊢ <;> exact finalFlow

#print axioms acceptedZeroGlobalEntryByteBody

end Goose.Proofs.ConstructionAcceptedExecution

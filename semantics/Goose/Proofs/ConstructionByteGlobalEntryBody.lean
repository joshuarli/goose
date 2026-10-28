import Goose.Proofs.ConstructionByteEntryFrameComplete
import Goose.Proofs.ConstructionByteGlobalEntryComplete

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedByteGlobalsEntryBody (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (initialized : ExecutionState) (declarations : List ByteOwnerDeclaration) (original : Context) (implementation : Impl)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (initializedRun : initGlobals (fuel + 3) config (List.range config.module.globals.size) .initial = .ok () initialized)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = declarations.map ByteOwnerDeclaration.statement)
    (owners : ∀ declaration ∈ declarations,
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (checkFuel : declarations.length ≤ 4094) :
    ∃ (frame next : ConstructionSourceFrame) (activation : RuntimeActivation)
      (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion),
      let environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
      let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
      let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let entryFrame := entryStatementsFrame config frame activated.nextScope
      let outcome := execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before
      let after := Goose.Proofs.Exit.stepState outcome
      runModule (fuel + 3) config .initial =
        (invokeCall (fuel + 3) config environment config.module.entry [] [] 0 >>= fun carriers => publishCarriers 0 carriers) initialized ∧
      invokeCall (fuel + 3) config environment config.module.entry [] [] 0 initialized =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated ∧
      frame.source.impl = implementation ∧ next.initialized = entryFrame.initialized ∧
      RootTypesExtend (declaredRootTypes config.module) types ∧
      AcceptedWorld config next.initialized after [.callChannels activation []] types live regions [] ∧
      AcceptedFrame config accepted next after types ∧
      (match outcome with | .ok flow _ => flow = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) := by
  obtain ⟨frame, activation, entryLive, moduleStep, callStep, environmentEq, world, source, position, phase, results⟩ :=
    acceptedByteGlobalsEntry fuel config accepted initialized globals initializedRun
  let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
  let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
  have originFact := source.compatible.origin
  unfold SourceOrigin at originFact
  simp only [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame,
    RootInterpretation.enterScope, phase] at originFact
  obtain ⟨entry, calls, entryAt, implAt, originRest⟩ := originFact
  have entryEq : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
  subst entry
  have implementationEq : frame.source.impl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
  obtain ⟨next, types, live, regions, initializedEq, extended, finalWorld, finalSource, finalFlow⟩ :=
    entryByteStatements_accepted_world fuel config accepted frame activation activated before declarations entryLive
      world source position phase results (by simpa only [implementationEq] using body)
      (by simpa only [implementationEq] using owners) checkFuel
  exact ⟨frame, next, activation, types, live, regions, moduleStep, callStep, implementationEq, initializedEq, extended,
    finalWorld, finalSource, finalFlow⟩

#print axioms acceptedByteGlobalsEntryBody

end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionByteGlobalEntryBody
import Goose.Proofs.ConstructionExecutionProtocolLifecycle

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execActivationBody_statements_stopped (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (body : Block) (before after : ExecutionState) (stop : Goose.Core.Stop)
    (stopped : execStmts fuel config
      { activation with scopes := (body.scope, before.nextScope) :: activation.scopes } body.stmts
      (ownershipResultScopeState activation body.scope before) = .stop stop after) :
    execActivationBody (fuel + 1) config activation [] body before = .stop stop after := by
  cases body with
  | mk scope statements value =>
    simp only [Block.scope, Block.stmts] at stopped
    simp only [ownershipResultScopeState, beq_iff_eq] at stopped
    simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope,
      bindAll, stopped]

theorem byteEntry_statements_stopped_module (fuel : Nat) (config : EvalConfig) (initialized : ExecutionState)
    (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (after : ExecutionState) (stop : Goose.Core.Stop)
    (environmentEq : frame.interpretation.environment = activation)
    (moduleStep : runModule (fuel + 3) config .initial =
      (invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>= fun carriers => publishCarriers 0 carriers) initialized)
    (callStep :
      let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
      invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initialized =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated)
    (stopped :
      let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
      let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let entryFrame := entryStatementsFrame config frame activated.nextScope
      execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before = .stop stop after) :
    runModule (fuel + 3) config .initial = .stop stop after := by
  let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
  have stopped' : execStmts fuel config
      { activation with scopes := (frame.source.impl.body.scope, activated.nextScope) :: activation.scopes }
      frame.source.impl.body.stmts (ownershipResultScopeState activation frame.source.impl.body.scope activated) = .stop stop after := by
    simpa only [entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environmentEq] using stopped
  have bodyStop := execActivationBody_statements_stopped fuel config activation frame.source.impl.body activated after stop stopped'
  dsimp only [activated] at bodyStop
  rw [moduleStep]
  simp only [bind, callStep, finishActivation, bodyStop]

theorem acceptedByteModule_stopped_or_body_complete (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (declarations : List ByteOwnerDeclaration) (original : Context) (implementation : Impl)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = declarations.map ByteOwnerDeclaration.statement)
    (owners : ∀ declaration ∈ declarations,
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (checkFuel : declarations.length ≤ 4094) :
    (∃ stop after initialized ambient types live regions,
      runModule (fuel + 3) config .initial = .stop stop after ∧
      AcceptedWorld config initialized after ambient types live regions [] ∧
      DestinationTraceProtocol after.construction) ∨
    ∃ (initialized : ExecutionState) (frame next : ConstructionSourceFrame) (activation : RuntimeActivation)
      (after : ExecutionState) (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion),
      let environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
      let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
      let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let entryFrame := entryStatementsFrame config frame activated.nextScope
      runModule (fuel + 3) config .initial =
        (invokeCall (fuel + 3) config environment config.module.entry [] [] 0 >>= fun carriers => publishCarriers 0 carriers) initialized ∧
      execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before = .ok (.normal .unit) after ∧
      frame.source.impl = implementation ∧ next.initialized = entryFrame.initialized ∧
      RootTypesExtend (declaredRootTypes config.module) types ∧
      AcceptedWorld config next.initialized after [.callChannels activation []] types live regions [] ∧
      AcceptedFrame config accepted next after types := by
  rcases acceptedByteGlobalsEntryBodyOrStop fuel config accepted declarations original implementation globals
      originalAt implementationAt body owners checkFuel with stopped | entry
  · obtain ⟨stop, after, initialized, live, regions, moduleStop, bound, world⟩ := stopped
    have protocol := Goose.Proofs.ConstructionExecutionProtocol.runModule_destination_trace_protocol (fuel + 3) config
    simp only [moduleStop, Goose.Proofs.Exit.stepState] at protocol
    exact Or.inl ⟨stop, after, initialized, [], declaredRootTypes config.module, live, regions, moduleStop, world, protocol⟩
  · obtain ⟨initialized, frame, next, activation, types, live, regions, initializedRun, moduleStep, callStep,
      implementationEq, environmentEq, initializedEq, extended, world, source, flow⟩ := entry
    let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
    let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
    let entryFrame := entryStatementsFrame config frame activated.nextScope
    change AcceptedWorld config next.initialized
      (Goose.Proofs.Exit.stepState (execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before))
      [.callChannels activation []] types live regions [] at world
    change AcceptedFrame config accepted next
      (Goose.Proofs.Exit.stepState (execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before)) types at source
    change (match execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
      | .ok result _ => result = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) at flow
    cases outcome : execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
    | stop stop after =>
      have moduleStop := byteEntry_statements_stopped_module fuel config initialized frame activation after stop
        environmentEq moduleStep callStep outcome
      simp only [outcome, Goose.Proofs.Exit.stepState] at world
      have protocol := Goose.Proofs.ConstructionExecutionProtocol.runModule_destination_trace_protocol (fuel + 3) config
      simp only [moduleStop, Goose.Proofs.Exit.stepState] at protocol
      exact Or.inl ⟨stop, after, next.initialized, [.callChannels activation []], types, live, regions, moduleStop, world, protocol⟩
    | ok result after =>
      simp only [outcome] at flow
      subst result
      simp only [outcome, Goose.Proofs.Exit.stepState] at world source
      exact Or.inr ⟨initialized, frame, next, activation, after, types, live, regions, moduleStep, outcome,
        implementationEq, initializedEq, extended, world, source⟩
    | escape target carriers after | jump target kind after =>
      simp only [outcome] at flow

#print axioms execActivationBody_statements_stopped
#print axioms byteEntry_statements_stopped_module
#print axioms acceptedByteModule_stopped_or_body_complete

end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionAcceptedScopeWorld
import Goose.Proofs.ConstructionByteEntryFrameComplete

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

theorem execActivationBody_empty_normal (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (body : Block) (before after : ExecutionState)
    (channels : activation.channels = []) (tail : body.value = none)
    (normal : execStmts fuel config
      { activation with scopes := (body.scope, before.nextScope) :: activation.scopes } body.stmts
      (ownershipResultScopeState activation body.scope before) = .ok (.normal .unit) after) :
    execActivationBody (fuel + 1) config activation [] body before =
      .ok [] (releaseScopeState activation body.scope before.nextScope after) := by
  cases body with
  | mk scope statements value =>
    simp only [Block.scope, Block.stmts, Block.value] at normal tail ⊢
    subst value
    simp only [ownershipResultScopeState, beq_iff_eq, channels] at normal
    simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope,
      bindAll, channels, normal, releaseScope]

theorem acceptedByteEntry_normal_scope (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (live : Goose.Core.RootInst → Prop) (declarations : List ByteOwnerDeclaration)
    (original : Context) (implementation : Impl)
    (world : AcceptedWorld config config.module.globals.size state [] (declaredRootTypes config.module) live [] [])
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = declarations.map ByteOwnerDeclaration.statement)
    (tail : implementation.body.value = none)
    (owners : ∀ declaration ∈ declarations,
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (checkFuel : declarations.length ≤ 4094) :
    ∃ (frame next : ConstructionSourceFrame) (activation : RuntimeActivation)
      (types : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion),
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let entryFrame := entryStatementsFrame config frame activated.nextScope
      let outcome := execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before
      (match outcome with
      | .ok (.normal .unit) after =>
        execActivationBody (fuel + 1) config activation [] frame.source.impl.body activated =
          .ok [] (releaseScopeState activation frame.source.impl.body.scope activated.nextScope after) ∧
        AcceptedWorld config next.initialized (releaseScopeState activation frame.source.impl.body.scope activated.nextScope after)
          [.callChannels activation []] types
          (fun root => nextLive root ∧ (Goose.Proofs.Exit.runtimeScopeRoots activation frame.source.impl.body.scope activated.nextScope).contains root = false)
          regions []
      | .stop _ _ => True
      | _ => False) := by
  obtain ⟨frame, activation, environmentEq, act, scopes, channels, freshActed, freshScope, frameWorld, source,
    position, phase, parameters, results, entry, entryAt, implAt, implId, vars⟩ :=
    acceptedEntryPushedStatements config accepted state [] (declaredRootTypes config.module) live [] [] world
  have entryEq : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
  subst entry
  have implementationEq : frame.source.impl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
  let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
  let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
  let entryFrame := entryStatementsFrame config frame activated.nextScope
  obtain ⟨next, types, nextLive, regions, initializedEq, extended, finalWorld, finalSource, finalFlow⟩ :=
    entryByteStatements_accepted_world fuel config accepted frame activation activated before declarations live
      frameWorld source position phase results (by simpa only [implementationEq] using body)
      (by simpa only [implementationEq] using owners) checkFuel
  change (match execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
    | .ok result _ => result = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) at finalFlow
  change AcceptedWorld config next.initialized
    (Goose.Proofs.Exit.stepState (execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before))
    [.callChannels activation []] types nextLive regions [] at finalWorld
  refine ⟨frame, next, activation, types, nextLive, regions, ?_⟩
  change (match execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
    | .ok (.normal .unit) after => _ | .stop _ _ => True | _ => False)
  cases outcome : execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
  | stop reason after => trivial
  | escape address carriers after | jump target kind after => simp only [outcome] at finalFlow
  | ok flow after =>
    simp only [outcome] at finalFlow
    subst flow
    have normal : execStmts fuel config
      { activation with scopes := (frame.source.impl.body.scope, activated.nextScope) :: activation.scopes }
      frame.source.impl.body.stmts before = .ok (.normal .unit) after := by
      simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environmentEq] using outcome
    have finalWorld' : AcceptedWorld config next.initialized after [.callChannels activation []] types nextLive regions [] := by
      simpa only [outcome, Goose.Proofs.Exit.stepState] using finalWorld
    exact ⟨execActivationBody_empty_normal fuel config activation frame.source.impl.body activated after channels
      (by simpa only [implementationEq] using tail) normal,
      finalWorld'.releaseScope config next.initialized after [.callChannels activation []] types nextLive regions []
        activation frame.source.impl.body.scope activated.nextScope⟩

#print axioms execActivationBody_empty_normal
#print axioms acceptedByteEntry_normal_scope
end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionAcceptedMixedLocalModule
import Goose.Proofs.ConstructionMixedLocalTailPosition

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem acceptedMixedLocalEntry_replayBody (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (live : Goose.Core.RootInst → Prop)
    (original : Context) (implementation : Impl)
    (world : AcceptedWorld config config.module.globals.size state [] (declaredRootTypes config.module) live [] [])
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (form : MixedLocalStatements implementation.body.stmts)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ implementation.body.stmts →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id expression origin, .letS id expression origin ∈ implementation.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, implementation.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    :
    ∃ (frame next : ConstructionSourceFrame) (activation : RuntimeActivation)
      (types : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion),
        let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let entryFrame := entryStatementsFrame config frame activated.nextScope
      let outcome := execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before
      activation.channels = [] ∧ frame.initialized = config.module.globals.size ∧
      frame.source.impl = implementation ∧ frame.interpretation.environment = activation ∧
      invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 state =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated ∧
      frame.phase = .implementation config.module.entry ∧ SourceFrameCompatible accepted entryFrame ∧
      next.initialized = config.module.globals.size ∧
      AcceptedWorld config next.initialized (Goose.Proofs.Exit.stepState outcome) [.callChannels activation []] types nextLive regions [] ∧
      (match outcome with | .ok flow _ => flow = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) ∧
      AcceptedFrame config accepted next (Goose.Proofs.Exit.stepState outcome) types ∧
      next.source = entryFrame.source ∧ next.interpretation = entryFrame.interpretation ∧ next.phase = entryFrame.phase ∧
      next.typing.globalLimit = entryFrame.typing.globalLimit ∧ GlobalEffectTargetsBounded next.rootCursor.eff config.module.globals.size ∧
      (match outcome with
      | .ok _ _ => typeStatements entryFrame.typingFuel entryFrame.typing frame.source.impl.body.stmts entryFrame.typingCounter =
            .ok (next.typing, next.typingCounter) ∧
          rpStmts entryFrame.source frame.source.impl.body.stmts entryFrame.rootCursor = .ok ((), next.rootCursor)
      | _ => True) := by
  obtain ⟨frame, activation, initialEq, environmentEq, act, scopes, channels, freshActed, freshScope, frameWorld, source,
    position, phase, parameters, results, entry, entryAt, implAt, implId, vars⟩ :=
    acceptedEntryPushedStatements_withInitialized config accepted state [] (declaredRootTypes config.module) live [] [] world
  have entryEq : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
  subst entry
  have implementationEq : frame.source.impl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
  have depth : state.activations.length < Goose.Core.maxCallDepth := by
    have runtime := world.ownership.runtime.activations
    cases active : state.activations with
    | nil => simp [Goose.Core.maxCallDepth]
    | cons head tail => simp [active, OwnershipAmbient.activations] at runtime
  have canonical : activation = ⟨original.impl, state.nextAct, frame.source.impl.vars, [], []⟩ := by
    cases activation with
    | mk impl act' vars' scopes' channels' =>
      simp only at implId act vars scopes channels
      cases implId
      cases act
      cases vars
      cases scopes
      cases channels
      rfl
  have step := entryCallStep (fuel + 1) config ⟨0, 0, #[], [], []⟩ state original frame.source.impl originalAt implAt
    parameters results depth
  simp only [Nat.add_assoc] at step
  rw [← canonical] at step
  have lookup : config.module.impls[activation.implementation]? = some frame.source.impl := by
    rw [implId]
    exact implAt
  have entryAction : enterActivation (fuel + 2) config activation [] frame.source.impl.body 0 =
      finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) := by
    funext current
    simp only [enterActivation, lookup, results, Array.toList_empty, List.map_nil]
  rw [entryAction] at step
  let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
  let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
  let entryFrame := entryStatementsFrame config frame activated.nextScope
  let full := entryFrame
  let types := declaredRootTypes config.module
  have form' : MixedLocalStatements frame.source.impl.body.stmts := by rw [implementationEq]; exact form
  have fullSource : AcceptedFrame config accepted full before types := source
  have fullWorld : AcceptedWorld config full.initialized before [.callChannels activation []] types live [] [] := frameWorld
  have fullPosition : SourcePosition accepted full (.statements frame.source.impl.body.stmts) := position
  have initialized : full.initialized = config.module.globals.size := by
    simpa only [full, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using initialEq
  have limit : full.typing.globalLimit ≤ config.module.globals.size := by
    simp [full, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame]
  have initialBound : GlobalEffectTargetsBounded full.rootCursor.eff config.module.globals.size := by
    simp [GlobalEffectTargetsBounded, Eff.accessTargets, full, entryFrame, entryStatementsFrame,
      blockStatementsFrame, implementationBodyFrame, parameters]
  have owners' : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ frame.source.impl.body.stmts →
      (full.source.impl.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)) := by
    intro declaration member
    simpa only [full, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, implementationEq] using
      owners declaration (by simpa only [implementationEq] using member)
  have scalarOwners' : ∀ id expression origin, .letS id expression origin ∈ frame.source.impl.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, full.source.impl.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
    intro id expression origin member shape descriptor declared
    apply scalarOwners id expression origin (by simpa only [implementationEq] using member) shape descriptor
    simpa only [full, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, implementationEq] using declared
  have unnamed : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ frame.source.impl.body.stmts →
      (full.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none := by
    intro declaration member
    simp only [full, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, results,
      Array.toList_empty, List.zipIdx_nil, List.find?_nil]
  obtain ⟨next, finalTypes, nextLive, regions, initializedEq, extended, finalWorld, finalSource, finalFlow, finalSourceEq, finalInterpretationEq, finalPhaseEq, finalLimitEq, finalBounded, finalReplay⟩ :=
    execStmts_mixedLocal_replay_world form' fuel config accepted full config.module.entry before
      [.callChannels activation []] types live [] [] fullWorld fullSource phase fullPosition initialized limit initialBound owners' scalarOwners' unnamed
  change (match execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
    | .ok result _ => result = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) at finalFlow
  change AcceptedWorld config next.initialized
    (Goose.Proofs.Exit.stepState (execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before))
    [.callChannels activation []] finalTypes nextLive regions [] at finalWorld
  have nextFull : next.initialized = config.module.globals.size := initializedEq.trans initialized
  exact ⟨frame, next, activation, finalTypes, nextLive, regions, channels, initialEq, implementationEq, environmentEq,
    step, phase, source.compatible, nextFull, finalWorld, finalFlow, finalSource, finalSourceEq, finalInterpretationEq, finalPhaseEq, finalLimitEq, finalBounded, finalReplay⟩

#print axioms acceptedMixedLocalEntry_replayBody
end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionAcceptedMixedTerminal
import Goose.Proofs.ConstructionMixedLocalEntryReplay

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem acceptedEntry_checkedSequenceEmptyRegionsWithScopes (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (live : Goose.Core.RootInst → Prop) {initialTypes : RootTypes} (original : Context) (implementation : Impl)
    (world : AcceptedWorld config config.module.globals.size state [] initialTypes live [] [])
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (sequence : ∀ (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (before : ExecutionState)
      (types : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (scopeInst : Nat),
      AcceptedWorld config frame.initialized before [.callChannels activation []] types nextLive [] [] →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation config.module.entry →
      frame.source.impl = implementation →
      frame.interpretation.environment.scopes = (implementation.body.scope, scopeInst) :: activation.scopes →
      activation.scopes = [] → activation.channels = [] →
      SourcePosition accepted frame (.statements implementation.body.stmts) →
      frame.initialized = config.module.globals.size → frame.typing.globalLimit ≤ config.module.globals.size →
      GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size →
      StatementWorldOutcome config accepted frame.initialized [.callChannels activation []] []
        (execStmts fuel config frame.interpretation.environment implementation.body.stmts before)) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation),
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let entryFrame := entryStatementsFrame config frame activated.nextScope
      activation.channels = [] ∧ frame.source.impl = implementation ∧ frame.interpretation.environment = activation ∧
      entryFrame.initialized = config.module.globals.size ∧
      invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 state =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated ∧
      StatementWorldOutcome config accepted entryFrame.initialized [.callChannels activation []] []
        (execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before) := by
  obtain ⟨frame, activation, initialEq, environmentEq, act, scopes, channels, freshActed, freshScope, frameWorld, source,
    position, phase, parameters, results, entry, entryAt, implAt, implId, vars⟩ :=
    acceptedEntryPushedStatements_withInitialized config accepted state [] initialTypes live [] [] world
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
  let types := initialTypes
  have fullSource : AcceptedFrame config accepted full before types := source
  have fullWorld : AcceptedWorld config full.initialized before [.callChannels activation []] types live [] [] := frameWorld
  have initialized : full.initialized = config.module.globals.size := by
    simpa only [full, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using initialEq
  have limit : full.typing.globalLimit ≤ config.module.globals.size := by
    simp [full, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame]
  have initialBound : GlobalEffectTargetsBounded full.rootCursor.eff config.module.globals.size := by
    simp [GlobalEffectTargetsBounded, Eff.accessTargets, full, entryFrame, entryStatementsFrame,
      blockStatementsFrame, implementationBodyFrame, parameters]
  have fullPosition : SourcePosition accepted full (.statements implementation.body.stmts) := by
    simpa [full, implementationEq] using position
  have sourceImpl : full.source.impl = implementation := by
    simpa [full, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using implementationEq
  have frameScopes : full.interpretation.environment.scopes =
      (frame.source.impl.body.scope, activated.nextScope) :: activation.scopes := by
    simp [full, entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environmentEq]
  have outcome := sequence full activation before types live activated.nextScope fullWorld fullSource phase sourceImpl
    (by simpa [implementationEq] using frameScopes) scopes channels fullPosition initialized limit initialBound
  refine ⟨frame, activation, channels, implementationEq, environmentEq, initialized, step, ?_⟩
  simpa [full, entryFrame, activated, before, implementationEq] using outcome

theorem acceptedEntry_checkedSequenceWithScopes (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (live : Goose.Core.RootInst → Prop) {initialTypes : RootTypes} (original : Context) (implementation : Impl)
    (world : AcceptedWorld config config.module.globals.size state [] initialTypes live [] [])
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (sequence : ∀ (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (before : ExecutionState)
      (types : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (scopeInst : Nat),
      AcceptedWorld config frame.initialized before [.callChannels activation []] types nextLive regions [] →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation config.module.entry →
      frame.source.impl = implementation →
      frame.interpretation.environment.scopes = (implementation.body.scope, scopeInst) :: activation.scopes →
      activation.scopes = [] →
      SourcePosition accepted frame (.statements implementation.body.stmts) →
      frame.initialized = config.module.globals.size → frame.typing.globalLimit ≤ config.module.globals.size →
      GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size →
      StatementWorldOutcome config accepted frame.initialized [.callChannels activation []] []
        (execStmts fuel config frame.interpretation.environment implementation.body.stmts before)) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation),
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let entryFrame := entryStatementsFrame config frame activated.nextScope
      activation.channels = [] ∧ frame.source.impl = implementation ∧ frame.interpretation.environment = activation ∧
      entryFrame.initialized = config.module.globals.size ∧
      invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 state =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated ∧
      StatementWorldOutcome config accepted entryFrame.initialized [.callChannels activation []] []
        (execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before) := by
  apply acceptedEntry_checkedSequenceEmptyRegionsWithScopes fuel config accepted state live original implementation world originalAt implementationAt
  intro frame activation before types nextLive scopeInst currentWorld currentSource phase sameImpl currentScopes activationEmpty channels position initialized limit bounded
  exact sequence frame activation before types nextLive [] scopeInst currentWorld currentSource phase sameImpl currentScopes activationEmpty position initialized limit bounded

theorem acceptedEntry_checkedSequence (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (live : Goose.Core.RootInst → Prop) {initialTypes : RootTypes} (original : Context) (implementation : Impl)
    (world : AcceptedWorld config config.module.globals.size state [] initialTypes live [] [])
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (sequence : ∀ (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (before : ExecutionState)
      (types : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (scopeInst : Nat),
      AcceptedWorld config frame.initialized before [.callChannels activation []] types nextLive regions [] →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation config.module.entry →
      frame.source.impl = implementation →
      frame.interpretation.environment.scopes = (implementation.body.scope, scopeInst) :: activation.scopes →
      SourcePosition accepted frame (.statements implementation.body.stmts) →
      frame.initialized = config.module.globals.size → frame.typing.globalLimit ≤ config.module.globals.size →
      GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size →
      StatementWorldOutcome config accepted frame.initialized [.callChannels activation []] []
        (execStmts fuel config frame.interpretation.environment implementation.body.stmts before)) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation),
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let entryFrame := entryStatementsFrame config frame activated.nextScope
      activation.channels = [] ∧ frame.source.impl = implementation ∧ frame.interpretation.environment = activation ∧
      entryFrame.initialized = config.module.globals.size ∧
      invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 state =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated ∧
      StatementWorldOutcome config accepted entryFrame.initialized [.callChannels activation []] []
        (execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before) := by
  apply acceptedEntry_checkedSequenceWithScopes fuel config accepted state live original implementation world originalAt implementationAt
  intro frame activation before types nextLive regions scopeInst currentWorld currentSource phase sameImpl currentScopes activationEmpty position initialized limit bounded
  exact sequence frame activation before types nextLive regions scopeInst currentWorld currentSource phase sameImpl currentScopes position initialized limit bounded

#print axioms acceptedEntry_checkedSequenceEmptyRegionsWithScopes
#print axioms acceptedEntry_checkedSequenceWithScopes
#print axioms acceptedEntry_checkedSequence
end Goose.Proofs.ConstructionAcceptedExecution

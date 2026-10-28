import Goose.Proofs.ConstructionAcceptedScalarRun
import Goose.Proofs.ConstructionByteGlobalEntryComplete

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

private theorem entryFrame_fullInitialization (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes) (context : Nat)
    (phase : frame.phase = .implementation context) (source : AcceptedFrame config accepted frame state types) :
    AcceptedFrame config accepted { frame with initialized := config.module.globals.size } state types := by
  have origin := source.compatible.origin
  have origin' : SourceOrigin accepted { frame with initialized := config.module.globals.size } := by
    simpa only [SourceOrigin, phase] using origin
  refine ⟨⟨source.compatible.module, source.compatible.rootModule, source.compatible.variables,
    source.compatible.sourceVariables, source.compatible.scopes, source.compatible.globalCount,
    source.compatible.globals, Nat.le_refl _, source.compatible.declarations, source.compatible.typingBound,
    source.compatible.visible, source.compatible.initializing, source.compatible.currentScope, origin'⟩,
    source.frontier, source.scopeFrontier, source.initializingBefore, source.aliases, source.locals, source.localTypes,
    source.uninitializedLocals, source.uninitializedTypes, ?_, source.direct, source.contents⟩
  intro id future within
  have lower : frame.initialized ≤ id := Nat.le_trans source.compatible.initialized future
  exact source.futureGlobals id lower within

private theorem unchangedConstruction_valueBacking (layout : LayoutEnv) (before after : ExecutionState)
    (value : Value) (same : after.construction = before.construction)
    (objects : after.objects = before.objects) (ordinals : after.objectOrdinals = before.objectOrdinals)
    (valid : ValueStorageBacked layout before value) : ValueStorageBacked layout after value := by
  induction valid with
  | integer ty number => exact .integer ty number
  | boolean value => exact .boolean value
  | unit => exact .unit
  | reference location => exact .reference location
  | slice location start count => exact .slice location start count
  | array values children ih => exact .array values ih
  | record id values children ih => exact .record id values ih
  | stored stored valid =>
    have frame : AllocationObservation before after stored.storage := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact objects
      · exact ordinals
      · rw [same]; exact Array.extract_size ..
      · rw [same]
    exact .stored stored (valid.allocation_frame layout before after stored frame)

private theorem entryWorld_extendGlobals (config : EvalConfig) (oldInitialized : Nat)
    (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (originalLive nextLive : Goose.Core.RootInst → Prop)
    (globalWorld : AcceptedWorld config config.module.globals.size before [] types originalLive [] [])
    (world : AcceptedWorld config oldInitialized after ambient types nextLive [] [])
    (construction : after.construction = before.construction) (objects : after.objects = before.objects)
    (ordinals : after.objectOrdinals = before.objectOrdinals) :
    AcceptedWorld config config.module.globals.size after ambient types (fun root => nextLive root ∨ originalLive root) [] [] := by
  have globals : GlobalRepresentations config.module config.module.globals.size after := by
    refine ⟨globalWorld.globals.1, ?_⟩
    intro id member
    obtain ⟨descriptor, value, declared, found, represented⟩ := globalWorld.globals.2 id member
    exact ⟨descriptor, value, declared, by rw [objects]; exact found, represented⟩
  have backing : RootedBackingState config.layout after (fun root => nextLive root ∨ originalLive root) := by
    refine ⟨?_, ?_⟩
    · intro root retained value found
      rcases retained with next | original
      · exact world.backing.values root next value found
      · exact unchangedConstruction_valueBacking config.layout before after value construction objects ordinals
          (globalWorld.backing.values root original value (by rw [objects] at found; exact found))
    · intro root retained stored found
      rcases retained with next | original
      · exact world.backing.identities root next stored found
      · rw [ordinals]
        exact globalWorld.backing.identities root original stored (by rw [objects] at found; exact found)
  refine ⟨⟨world.ownership, globals, world.globalTypes, world.layouts, world.typeFrontier, world.syntheticFrontier,
    world.heap, world.objectsRegistered, world.ordinalsRegistered, backing, ?_, ?_⟩, ?_⟩
  · intro region member; cases member
  · intro carrier member; cases member
  · intro id member; exact Or.inr (globalWorld.globalLive id member)

theorem acceptedByteGlobalsScalarEntry (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (initialized : ExecutionState)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (globals : initGlobals (fuel + 3) config (List.range config.module.globals.size) .initial = .ok () initialized)
    (original : Context) (implementation : Impl)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (form : ScalarExpressionStatements implementation.body.stmts) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (live : Goose.Core.RootInst → Prop),
      let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
      let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let next := entryStatementsFrame config frame activated.nextScope
      let full := { next with initialized := config.module.globals.size }
      let outcome := execStmts fuel config full.interpretation.environment frame.source.impl.body.stmts after
      Goose.Proofs.Exit.stepState outcome = after ∧
      AcceptedWorld config full.initialized (Goose.Proofs.Exit.stepState outcome) [.callChannels activation []]
        (declaredRootTypes config.module) live [] [] ∧
      AcceptedFrame config accepted full (Goose.Proofs.Exit.stepState outcome) (declaredRootTypes config.module) ∧
      (∀ reason final, outcome = .stop reason final → runModule (fuel + 3) config .initial = .stop reason final) := by
  have globalRun : initGlobals ((fuel + 2) + 1) config (List.range config.module.globals.size) .initial = .ok () initialized := by
    simpa only [Nat.add_assoc] using globals
  obtain ⟨originalLive, globalWorld, _⟩ := initGlobals_byteOwners_initial (fuel + 2) config accepted initialized declarations globalRun
  obtain ⟨frame, activation, nextLive, moduleStep, callStep, environmentEq, world, source, position, phase, results⟩ :=
    acceptedByteGlobalsEntry fuel config accepted initialized declarations globals
  let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
  let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
  let next := entryStatementsFrame config frame activated.nextScope
  let full := { next with initialized := config.module.globals.size }
  let live := fun root => nextLive root ∨ originalLive root
  have originFact := source.compatible.origin
  unfold SourceOrigin at originFact
  simp only [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame,
    RootInterpretation.enterScope, phase] at originFact
  obtain ⟨entry, calls, entryAt, implAt, originRest⟩ := originFact
  have entryEq : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
  subst entry
  have implementationEq : frame.source.impl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
  have form' : ScalarExpressionStatements frame.source.impl.body.stmts := by rw [implementationEq]; exact form
  have fullPhase : next.phase = .implementation config.module.entry := phase
  have fullSource : AcceptedFrame config accepted full after (declaredRootTypes config.module) :=
    entryFrame_fullInitialization config accepted next after (declaredRootTypes config.module) config.module.entry fullPhase source
  have fullWorld : AcceptedWorld config full.initialized after [.callChannels activation []] (declaredRootTypes config.module) live [] [] :=
    entryWorld_extendGlobals config next.initialized initialized after [.callChannels activation []] (declaredRootTypes config.module)
      originalLive nextLive globalWorld world rfl rfl rfl
  have fullPosition : SourcePosition accepted full (.statements frame.source.impl.body.stmts) :=
    position.instantiate next.interpretation config.module.globals.size
  have limit : full.typing.globalLimit ≤ config.module.globals.size := by
    simp [full, next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame]
  have initialBound : GlobalEffectTargetsBounded full.rootCursor.eff config.module.globals.size := by
    simp [GlobalEffectTargetsBounded, Eff.accessTargets, full, next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame]
  have count : full.interpretation.globalCount = config.module.globals.size := source.compatible.globalCount
  have available : ∀ final, rpStmts full.source frame.source.impl.body.stmts full.rootCursor = .ok ((), final) →
      GlobalEffectsAvailable full.interpretation full.initialized final.eff := by
    intro final rooted
    have bound := form'.effects_bounded config accepted full config.module.globals.size fullPosition limit initialBound final rooted
    change GlobalEffectsAvailable full.interpretation config.module.globals.size final.eff
    rw [← count]
    exact (globalEffectsAvailable_iff_bounded full.interpretation final.eff).2 (by simpa only [count] using bound)
  have result := fullPosition.scalarStatements_complete accepted full frame.source.impl.body.stmts form' available fuel after
    [.callChannels activation []] (declaredRootTypes config.module) live [] [] fullWorld fullSource
  refine ⟨frame, activation, live, result.1, result.2.2.1, result.2.2.2, ?_⟩
  intro reason final stopped
  have action : execActivationBody (fuel + 1) config activation [] frame.source.impl.body activated = .stop reason final := by
    cases body : frame.source.impl.body with
    | mk scope statements tail =>
      simp only [body] at stopped ⊢
      have stopped' : execStmts fuel config { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
          statements (ownershipResultScopeState activation scope activated) = .stop reason final := by
        simpa [full, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environmentEq,
          implementationBodyFrame, body, Block.scope, Block.stmts, activated] using stopped
      simp only [execActivationBody, bind]
      rw [execResultScope_ownership_continuation]
      simp only [bindAll, List.forIn_nil, pure, bind, withScope, stopped']
  have invoked : invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initialized = .stop reason final := by
    rw [callStep]
    change ((finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>=
      fun carriers => deliverCarriers (fuel + 2) config.layout [] carriers 0) activated) = .stop reason final
    simp only [bind, finishActivation, action]
  rw [moduleStep]
  change ((invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>=
    fun carriers => publishCarriers 0 carriers) initialized) = .stop reason final
  simp only [bind, invoked]

theorem acceptedByteGlobalsScalarRun (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (original : Context) (implementation : Impl)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (form : ScalarExpressionStatements implementation.body.stmts) :
    (∃ stop after completed live regions,
      runModule (fuel + 3) config .initial = .stop stop after ∧
      completed < config.module.globals.size ∧
      AcceptedWorld config completed after [] (declaredRootTypes config.module) live regions []) ∨
    ∃ (initialized : ExecutionState) (frame : ConstructionSourceFrame) (activation : RuntimeActivation)
      (live : Goose.Core.RootInst → Prop),
      let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
      let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let next := entryStatementsFrame config frame activated.nextScope
      let full := { next with initialized := config.module.globals.size }
      let outcome := execStmts fuel config full.interpretation.environment frame.source.impl.body.stmts after
      initGlobals (fuel + 3) config (List.range config.module.globals.size) .initial = .ok () initialized ∧
      Goose.Proofs.Exit.stepState outcome = after ∧
      AcceptedWorld config full.initialized (Goose.Proofs.Exit.stepState outcome) [.callChannels activation []]
        (declaredRootTypes config.module) live [] [] ∧
      AcceptedFrame config accepted full (Goose.Proofs.Exit.stepState outcome) (declaredRootTypes config.module) ∧
      (∀ reason final, outcome = .stop reason final → runModule (fuel + 3) config .initial = .stop reason final) := by
  rcases acceptedByteGlobalsEntryOrStop fuel config accepted declarations with stopped | entry
  · exact Or.inl stopped
  · obtain ⟨initialized, _, _, _, globals, _⟩ := entry
    obtain ⟨frame, activation, live, result⟩ := acceptedByteGlobalsScalarEntry fuel config accepted initialized declarations globals
      original implementation originalAt implementationAt form
    exact Or.inr ⟨initialized, frame, activation, live, globals, result⟩

#print axioms acceptedByteGlobalsScalarRun
#print axioms acceptedByteGlobalsScalarEntry
#print axioms entryWorld_extendGlobals
#print axioms entryFrame_fullInitialization
end Goose.Proofs.ConstructionAcceptedExecution

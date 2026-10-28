import Goose.Proofs.ConstructionAcceptedRegisterCallTail

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem invokeCall_register_compose (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target : Nat) (context : Context) (implementation : Impl) (ty : Ty) (origin : Nat)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (clear : FutureGlobalsClear config initialized state)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[]) (results : implementation.results = #[⟨ty, .register, none⟩])
    (bodySafe :
      let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
      let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      ∃ nextTypes nextLive nextAmbient,
        let outcome := execActivationBody fuel config activation [] implementation.body pushed
        RootTypesExtend types nextTypes ∧
        pushed.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        pushed.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
        FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
        (match outcome with
         | .ok carriers _ => nextAmbient = .callChannels activation [] :: ambient ∧
             ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
         | .stop .. => True
         | .escape .. | .jump .. => False)) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := invokeCall (fuel + 2) config environment target [] [.register ty] origin state
      RootTypesExtend types nextTypes ∧
      state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True
       | .escape .. | .jump .. => False) := by
  have transition := invokeCall_zeroArgument_register_transition fuel config environment target context
    implementation ty origin state contextAt implementationAt parameters results
  by_cases depth : state.activations.length ≥ Goose.Core.maxCallDepth
  · simp only [depth, ↓reduceIte] at transition
    rw [transition]
    exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, clear, trivial⟩
  · simp only [depth, ↓reduceIte] at transition
    let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
    let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
    change ∃ nextTypes nextLive nextAmbient, let outcome := execActivationBody fuel config activation [] implementation.body pushed; _ at bodySafe
    obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, bodyWorld, bodyClear, bodyResult⟩ := bodySafe
    have calleeAt : config.module.impls[activation.implementation]? = some implementation := by
      simpa [activation] using implementationAt
    cases execution : execActivationBody fuel config activation [] implementation.body pushed with
    | stop reason after =>
      simp only [activation, pushed] at execution
      simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes bodyWorld bodyClear bodyResult
      have entered : enterActivation (fuel + 1) config activation [] implementation.body origin pushed = .stop reason after := by
        simp [enterActivation, calleeAt, finishActivation, activation, pushed, execution]
      have callRun : invokeCall (fuel + 2) config environment target [] [.register ty] origin state = .stop reason after := by
        rw [transition]
        change (do let carriers ← enterActivation (fuel + 1) config activation [] implementation.body origin
                   deliverCarriers (fuel + 1) config.layout [.register ty] carriers origin) pushed = _
        simp only [bind, entered]
      rw [callRun]
      exact ⟨nextTypes, nextLive, nextAmbient, extend, Nat.le_trans (Nat.le_succ _) acts, scopes, bodyWorld, bodyClear, trivial⟩
    | escape address carriers after | jump destination kind after =>
      simp only [activation, pushed] at execution
      simp [execution] at bodyResult
    | ok carriers after =>
      simp only [activation, pushed] at execution
      simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes bodyWorld bodyClear bodyResult
      obtain ⟨rfl, value, rfl, represented⟩ := bodyResult
      have finished := finishActivation_register_normal config initialized activation ambient nextTypes nextLive regions pending
        ty origin (execActivationBody fuel config activation [] implementation.body) pushed after value
        rfl execution bodyWorld bodyClear
      obtain ⟨finishedRun, finishedWorld, finishedClear⟩ := finished
      have entered : enterActivation (fuel + 1) config activation [] implementation.body origin pushed =
          .ok [.register value] { after with activations := after.activations.filter (fun current => current.act != activation.act) } := by
        simpa [enterActivation, calleeAt, results] using finishedRun
      have callRun : invokeCall (fuel + 2) config environment target [] [.register ty] origin state =
          .ok [.register value] { after with activations := after.activations.filter (fun current => current.act != activation.act) } := by
        rw [transition]
        change (do let carriers ← enterActivation (fuel + 1) config activation [] implementation.body origin
                   deliverCarriers (fuel + 1) config.layout [.register ty] carriers origin) pushed = _
        simpa only [bind, entered] using deliverCarriers_register (fuel + 1) config.layout ty value origin
          { after with activations := after.activations.filter (fun current => current.act != activation.act) }
      rw [callRun]
      exact ⟨nextTypes, nextLive, ambient, extend, Nat.le_trans (Nat.le_succ _) acts, scopes, finishedWorld,
        finishedClear, rfl, value, rfl, represented⟩

theorem SourcePosition.callee_registerCall_withArguments_tail_checked {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (scope target origin : Nat) (context : Context)
    (callee : Impl) (ty : Ty) (arguments : List Arg)
    (bodyFrame : implementationBodyFrame config frame = frame)
    (body : frame.source.impl.body = ⟨scope, [], some (.call target arguments origin)⟩)
    (position : SourcePosition accepted frame (.block ⟨scope, [], some (.call target arguments origin)⟩))
    (contextAt : frame.typing.module.contexts[target]? = some context)
    (calleeAt : frame.typing.module.impls[context.impl]? = some callee)
    (results : callee.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (requests : frame.typing.resultRequests = [.register])
    (available : ∀ result after, rpBlockValue frame.source [] ⟨scope, [], some (.call target arguments origin)⟩ frame.rootCursor =
      .ok (result, after) → GlobalEffectsAvailable frame.interpretation frame.initialized after.eff) :
    ∃ roots typingAfter rootsAfter,
      CheckedValue (entryStatementsFrame config frame state.nextScope) (.call target arguments origin) ty roots typingAfter rootsAfter := by
  have nesting : frame.typingFuel = 4095 + 1 := by
    have fixed := congrArg (fun f : ConstructionSourceFrame => f.typingFuel) bodyFrame
    simpa [implementationBodyFrame] using fixed.symm
  obtain ⟨roots, typingAfter, rootsAfter, checked⟩ := position.emptyBlock_registerCall_withArguments_checked accepted frame scope 4095 target origin
    context callee ty arguments nesting contextAt calleeAt results scalar requests available
  refine ⟨roots, typingAfter, rootsAfter, ?_⟩
  constructor
  · simpa [entryStatementsFrame, blockStatementsFrame, bodyFrame, body, Block.scope] using checked.typing
  · simpa [entryStatementsFrame, blockStatementsFrame, bodyFrame, body, Block.scope] using checked.provenance
  · simpa [entryStatementsFrame, blockStatementsFrame, bodyFrame, body, Block.scope, RootInterpretation.enterScope,
      GlobalEffectsAvailable] using checked.available


theorem SourcePosition.callee_registerCall_tail_checked {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (scope target origin : Nat) (context : Context)
    (callee : Impl) (ty : Ty)
    (bodyFrame : implementationBodyFrame config frame = frame)
    (body : frame.source.impl.body = ⟨scope, [], some (.call target [] origin)⟩)
    (position : SourcePosition accepted frame (.block ⟨scope, [], some (.call target [] origin)⟩))
    (contextAt : frame.typing.module.contexts[target]? = some context)
    (calleeAt : frame.typing.module.impls[context.impl]? = some callee)
    (results : callee.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (requests : frame.typing.resultRequests = [.register])
    (available : ∀ result after, rpBlockValue frame.source [] ⟨scope, [], some (.call target [] origin)⟩ frame.rootCursor =
      .ok (result, after) → GlobalEffectsAvailable frame.interpretation frame.initialized after.eff) :
    ∃ roots typingAfter rootsAfter,
      CheckedValue (entryStatementsFrame config frame state.nextScope) (.call target [] origin) ty roots typingAfter rootsAfter := by
  exact position.callee_registerCall_withArguments_tail_checked accepted frame state scope target origin context callee ty [] bodyFrame body
    contextAt calleeAt results scalar requests available

theorem execActivationBody_checked_registerCall_compose (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (contextId : Nat) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (scope target origin : Nat) (context : Context) (callee : Impl) (ty : Ty)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation contextId)
    (parameters : frame.source.impl.params = #[]) (scopes : frame.interpretation.environment.scopes = [])
    (cursor : frame.rootCursor = ⟨0, {}, []⟩) (bodyFrame : implementationBodyFrame config frame = frame)
    (body : frame.source.impl.body = ⟨scope, [], some (.call target [] origin)⟩)
    (channels : frame.interpretation.environment.channels = [.register ty])
    (position : SourcePosition accepted frame (.block ⟨scope, [], some (.call target [] origin)⟩))
    (contextAt : frame.typing.module.contexts[target]? = some context)
    (calleeAt : frame.typing.module.impls[context.impl]? = some callee)
    (results : callee.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (requests : frame.typing.resultRequests = [.register])
    (available : ∀ result after, rpBlockValue frame.source [] ⟨scope, [], some (.call target [] origin)⟩ frame.rootCursor =
      .ok (result, after) → GlobalEffectsAvailable frame.interpretation frame.initialized after.eff)
    (inner : ∀ roots typingAfter rootsAfter,
      CheckedValue (entryStatementsFrame config frame state.nextScope) (.call target [] origin) ty roots typingAfter rootsAfter →
      AcceptedWorld config (entryStatementsFrame config frame state.nextScope).initialized
        (ownershipResultScopeState frame.interpretation.environment scope state) ambient types live regions pending →
      AcceptedFrame config accepted (entryStatementsFrame config frame state.nextScope)
        (ownershipResultScopeState frame.interpretation.environment scope state) types →
      ∃ nextTypes nextLive nextAmbient,
        let outcome := invokeCall fuel config
          { frame.interpretation.environment with scopes := (scope, state.nextScope) :: frame.interpretation.environment.scopes }
          target [] [.register ty] origin (ownershipResultScopeState frame.interpretation.environment scope state)
        RootTypesExtend types nextTypes ∧
        (ownershipResultScopeState frame.interpretation.environment scope state).nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        (ownershipResultScopeState frame.interpretation.environment scope state).nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
        FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
        (match outcome with
         | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
         | .stop .. => True | .escape .. | .jump .. => False)) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := execActivationBody (fuel + 2) config frame.interpretation.environment [] ⟨scope, [], some (.call target [] origin)⟩ state
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  obtain ⟨scopeWorld, scopeSource, _⟩ := acceptedCalleeBodyScope config accepted frame contextId state ambient types live regions pending
    world source phase parameters scopes cursor
  have bodyScope : frame.source.impl.body.scope = scope := by simp [body, Block.scope]
  rw [bodyScope] at scopeWorld scopeSource
  obtain ⟨roots, typingAfter, rootsAfter, checked⟩ := position.callee_registerCall_tail_checked accepted frame state scope target origin
    context callee ty bodyFrame body contextAt calleeAt results scalar requests available
  exact execActivationBody_empty_registerCall_compose fuel config frame.initialized frame.interpretation.environment scope ty target origin state
    ambient types regions pending channels (inner roots typingAfter rootsAfter checked scopeWorld scopeSource)

#print axioms execActivationBody_checked_registerCall_compose
#print axioms SourcePosition.callee_registerCall_withArguments_tail_checked
#print axioms SourcePosition.callee_registerCall_tail_checked
#print axioms invokeCall_register_compose
end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionAcceptedParameterizedScalarPrefix
import Goose.Proofs.ConstructionAcceptedParameterizedScalarReplay

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem execActivationBody_boundCheckedScalarPrefix_withReplay_earlier (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (blockFrame frame : ConstructionSourceFrame) (context : Nat) (activation : RuntimeActivation) (scope stamp : Nat)
    (pre : List (Nat × Value)) (statements : List Stmt) (target origin : Nat) (arguments : List Arg)
    (calleeContext : Context) (callee : Impl) (before boundState : ExecutionState) (ambient : OwnershipAmbient)
    (types boundTypes : RootTypes) (boundLive : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame) (ty : Ty) (frontier : Nat)
    (channels : activation.channels = [.register ty]) (frontierBound : frontier ≤ activation.act)
    (environment : frame.interpretation.environment = { activation with scopes := (scope, before.nextScope) :: activation.scopes })
    (bound : bindAll activation.act before.nextScope pre (ownershipResultScopeState activation scope before) = .ok () boundState)
    (extended : RootTypesExtend types boundTypes) (acts : before.nextAct ≤ boundState.nextAct) (scopes : before.nextScope ≤ boundState.nextScope)
    (observed : EarlierCallerObservations frontier before boundState types boundTypes)
    (world : AcceptedWorld config frame.initialized boundState ambient boundTypes boundLive regions pending)
    (source : AcceptedFrame config accepted frame boundState boundTypes) (phase : frame.phase = .implementation context)
    (statementsPosition : SourcePosition accepted frame (.statements statements)) (form : ScalarLocalStatements statements)
    (scalarStatements : ∀ id expression location, .letS id expression location ∈ statements → ∀ descriptor,
      frame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (position : SourcePosition accepted blockFrame (.block ⟨scope, statements, some (.call target arguments origin)⟩))
    (nesting : blockFrame.typingFuel = (checkFuel + 1) + 1)
    (childTyping : frame.typing = { blockFrame.typing with scope := scope })
    (childFuel : frame.typingFuel = checkFuel + 1) (childCounter : frame.typingCounter = blockFrame.typingCounter)
    (childSource : frame.source = { blockFrame.source with scopes := scope :: blockFrame.source.scopes })
    (childCursor : frame.rootCursor = blockFrame.rootCursor)
    (childInterpretation : frame.interpretation = blockFrame.interpretation.enterScope scope stamp)
    (childInitialized : frame.initialized = blockFrame.initialized)
    (contextAt : blockFrame.typing.module.contexts[target]? = some calleeContext)
    (calleeAt : blockFrame.typing.module.impls[calleeContext.impl]? = some callee)
    (results : callee.results = #[⟨ty, .register, none⟩]) (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (requests : blockFrame.typing.resultRequests = [.register])
    (available : ∀ result after, rpBlockValue blockFrame.source [] ⟨scope, statements, some (.call target arguments origin)⟩ blockFrame.rootCursor =
      .ok (result, after) → GlobalEffectsAvailable blockFrame.interpretation blockFrame.initialized after.eff)
    (inner : ∀ (final : ConstructionSourceFrame) (middle : ExecutionState) (middleTypes : RootTypes)
        (middleLive : Goose.Core.RootInst → Prop) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState),
      final.initialized = frame.initialized → middle.nextAct = boundState.nextAct → ScalarLocalReplay frame final statements →
      AcceptedWorld config final.initialized middle ambient middleTypes middleLive regions pending →
      AcceptedFrame config accepted final middle middleTypes →
      CheckedValue { final with typingFuel := checkFuel + 1 } (.call target arguments origin) ty roots typingAfter rootsAfter →
      ∃ finalTypes finalLive finalAmbient,
        let outcome := invokeCall fuel config frame.interpretation.environment target arguments [.register ty] origin middle
        RootTypesExtend middleTypes finalTypes ∧ middle.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        middle.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) finalAmbient finalTypes finalLive regions pending ∧
        FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
        EarlierCallerObservations frontier middle (Goose.Proofs.Exit.stepState outcome) middleTypes finalTypes ∧
        (match outcome with
         | .ok carriers _ => finalAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
         | .stop .. => True | .escape .. | .jump .. => False)) :
    ∃ finalTypes finalLive finalAmbient,
      let outcome := execActivationBody (fuel + 2) config activation pre ⟨scope, statements, some (.call target arguments origin)⟩ before
      RootTypesExtend types finalTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) finalAmbient finalTypes finalLive regions pending ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations frontier before (Goose.Proofs.Exit.stepState outcome) types finalTypes ∧
      (match outcome with
       | .ok carriers _ => finalAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  obtain ⟨middleRoots, _, _, rootedStatements, _, middleAvailable, _⟩ :=
    position.blockTail_effects accepted blockFrame scope statements (.call target arguments origin) available
  have seqAvailable : ∀ rootsAfter, rpStmts frame.source statements frame.rootCursor = .ok ((), rootsAfter) →
      GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff := by
    intro rootsAfter rooted
    have same : rootsAfter = middleRoots := by
      rw [childSource, childCursor] at rooted
      exact (Prod.mk.inj (Except.ok.inj (rooted.symm.trans rootedStatements))).2
    subst rootsAfter
    simpa [childInterpretation, RootInterpretation.enterScope, childInitialized, GlobalEffectsAvailable] using middleAvailable
  apply execActivationBody_boundScalarPrefix_withClock_earlier fuel config accepted frame context activation scope pre statements target origin arguments
    before boundState ambient types boundTypes boundLive regions pending ty frontier channels frontierBound environment bound extended acts scopes
    observed world source phase statementsPosition form seqAvailable scalarStatements
  intro final middle middleTypes middleLive initialized clock finalWorld finalSource replay
  obtain ⟨roots, typingAfter, rootsAfter, checked⟩ := replay.registerCall_withArguments_tail_checked_fromBlock accepted blockFrame frame final
    scope stamp checkFuel target origin statements calleeContext callee arguments ty position nesting childTyping childFuel childCounter childSource
    childCursor childInterpretation childInitialized initialized form contextAt calleeAt results scalarTy requests available
  exact inner final middle middleTypes middleLive roots typingAfter rootsAfter initialized clock replay finalWorld finalSource checked


theorem execActivationBody_boundCheckedScalarPrefix_earlier (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (blockFrame frame : ConstructionSourceFrame) (context : Nat) (activation : RuntimeActivation) (scope stamp : Nat)
    (pre : List (Nat × Value)) (statements : List Stmt) (target origin : Nat) (arguments : List Arg)
    (calleeContext : Context) (callee : Impl) (before boundState : ExecutionState) (ambient : OwnershipAmbient)
    (types boundTypes : RootTypes) (boundLive : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame) (ty : Ty) (frontier : Nat)
    (channels : activation.channels = [.register ty]) (frontierBound : frontier ≤ activation.act)
    (environment : frame.interpretation.environment = { activation with scopes := (scope, before.nextScope) :: activation.scopes })
    (bound : bindAll activation.act before.nextScope pre (ownershipResultScopeState activation scope before) = .ok () boundState)
    (extended : RootTypesExtend types boundTypes) (acts : before.nextAct ≤ boundState.nextAct) (scopes : before.nextScope ≤ boundState.nextScope)
    (observed : EarlierCallerObservations frontier before boundState types boundTypes)
    (world : AcceptedWorld config frame.initialized boundState ambient boundTypes boundLive regions pending)
    (source : AcceptedFrame config accepted frame boundState boundTypes) (phase : frame.phase = .implementation context)
    (statementsPosition : SourcePosition accepted frame (.statements statements)) (form : ScalarLocalStatements statements)
    (scalarStatements : ∀ id expression location, .letS id expression location ∈ statements → ∀ descriptor,
      frame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (position : SourcePosition accepted blockFrame (.block ⟨scope, statements, some (.call target arguments origin)⟩))
    (nesting : blockFrame.typingFuel = (checkFuel + 1) + 1)
    (childTyping : frame.typing = { blockFrame.typing with scope := scope })
    (childFuel : frame.typingFuel = checkFuel + 1) (childCounter : frame.typingCounter = blockFrame.typingCounter)
    (childSource : frame.source = { blockFrame.source with scopes := scope :: blockFrame.source.scopes })
    (childCursor : frame.rootCursor = blockFrame.rootCursor)
    (childInterpretation : frame.interpretation = blockFrame.interpretation.enterScope scope stamp)
    (childInitialized : frame.initialized = blockFrame.initialized)
    (contextAt : blockFrame.typing.module.contexts[target]? = some calleeContext)
    (calleeAt : blockFrame.typing.module.impls[calleeContext.impl]? = some callee)
    (results : callee.results = #[⟨ty, .register, none⟩]) (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (requests : blockFrame.typing.resultRequests = [.register])
    (available : ∀ result after, rpBlockValue blockFrame.source [] ⟨scope, statements, some (.call target arguments origin)⟩ blockFrame.rootCursor =
      .ok (result, after) → GlobalEffectsAvailable blockFrame.interpretation blockFrame.initialized after.eff)
    (inner : ∀ (final : ConstructionSourceFrame) (middle : ExecutionState) (middleTypes : RootTypes)
        (middleLive : Goose.Core.RootInst → Prop) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState),
      final.initialized = frame.initialized →
      AcceptedWorld config final.initialized middle ambient middleTypes middleLive regions pending →
      AcceptedFrame config accepted final middle middleTypes →
      CheckedValue { final with typingFuel := checkFuel + 1 } (.call target arguments origin) ty roots typingAfter rootsAfter →
      ∃ finalTypes finalLive finalAmbient,
        let outcome := invokeCall fuel config frame.interpretation.environment target arguments [.register ty] origin middle
        RootTypesExtend middleTypes finalTypes ∧ middle.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        middle.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) finalAmbient finalTypes finalLive regions pending ∧
        FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
        EarlierCallerObservations frontier middle (Goose.Proofs.Exit.stepState outcome) middleTypes finalTypes ∧
        (match outcome with
         | .ok carriers _ => finalAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
         | .stop .. => True | .escape .. | .jump .. => False)) :
    ∃ finalTypes finalLive finalAmbient,
      let outcome := execActivationBody (fuel + 2) config activation pre ⟨scope, statements, some (.call target arguments origin)⟩ before
      RootTypesExtend types finalTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) finalAmbient finalTypes finalLive regions pending ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations frontier before (Goose.Proofs.Exit.stepState outcome) types finalTypes ∧
      (match outcome with
       | .ok carriers _ => finalAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  apply execActivationBody_boundCheckedScalarPrefix_withReplay_earlier fuel checkFuel config accepted blockFrame frame context activation scope stamp
    pre statements target origin arguments calleeContext callee before boundState ambient types boundTypes boundLive regions pending ty frontier
    channels frontierBound environment bound extended acts scopes observed world source phase statementsPosition form scalarStatements position nesting
    childTyping childFuel childCounter childSource childCursor childInterpretation childInitialized contextAt calleeAt results scalarTy requests available
  intro final middle middleTypes middleLive roots typingAfter rootsAfter initialized _ _ finalWorld finalSource checked
  exact inner final middle middleTypes middleLive roots typingAfter rootsAfter initialized finalWorld finalSource checked

#print axioms execActivationBody_boundCheckedScalarPrefix_withReplay_earlier
#print axioms execActivationBody_boundCheckedScalarPrefix_earlier
end Goose.Proofs.ConstructionAcceptedExecution

import Goose.Proofs.ConstructionAcceptedRecursiveCallLocalTail
import Goose.Proofs.ConstructionAcceptedEarlierCallerObservations

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execActivationBody_registerCall_earlierObservations (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt) (ty : Ty) (target origin : Nat)
    (before middle : ExecutionState) (frontier : Nat) (types nextTypes : RootTypes)
    (bound : frontier ≤ activation.act) (channels : activation.channels = [.register ty])
    (normal : execStmts (fuel + 1) config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements
      (ownershipResultScopeState activation scope before) = .ok (.normal .unit) middle)
    (inner : EarlierCallerObservations frontier middle
      (Goose.Proofs.Exit.stepState (invokeCall fuel config
        { activation with scopes := (scope, before.nextScope) :: activation.scopes }
        target [] [.register ty] origin middle)) types nextTypes) :
    EarlierCallerObservations frontier middle
      (Goose.Proofs.Exit.stepState (execActivationBody (fuel + 2) config activation []
        ⟨scope, statements, some (.call target [] origin)⟩ before)) types nextTypes := by
  let environment := { activation with scopes := (scope, before.nextScope) :: activation.scopes }
  have body := execActivationBody_register_call_tail fuel config activation scope statements before middle ty target origin channels normal
  cases execution : invokeCall fuel config environment target [] [.register ty] origin middle with
  | stop reason after =>
    simp only [environment] at execution
    simp only [execution, Goose.Proofs.Exit.stepState] at inner
    rw [body, execution]
    exact inner
  | ok carriers after | escape address carriers after | jump destination kind after =>
    simp only [environment] at execution
    simp only [execution, Goose.Proofs.Exit.stepState] at inner
    rw [body, execution]
    exact inner.trans (Nat.le_refl _) (EarlierCallerObservations.releaseScope frontier activation scope before.nextScope after nextTypes bound)

theorem execActivationBody_scalarLocal_registerCall_earlier (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context : Nat) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (frontier scope : Nat) (statements : List Stmt) (target origin : Nat) (calleeContext : Context) (callee : Impl) (ty : Ty)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation context)
    (parameters : frame.source.impl.params = #[]) (scopes : frame.interpretation.environment.scopes = [])
    (cursor : frame.rootCursor = ⟨0, {}, []⟩) (bodyFrame : implementationBodyFrame config frame = frame)
    (body : frame.source.impl.body = ⟨scope, statements, some (.call target [] origin)⟩)
    (frontierBound : frontier ≤ frame.interpretation.environment.act)
    (channels : frame.interpretation.environment.channels = [.register ty])
    (position : SourcePosition accepted frame (.block ⟨scope, statements, some (.call target [] origin)⟩))
    (form : ScalarLocalStatements statements)
    (scalar : ∀ id expression origin, .letS id expression origin ∈ statements → ∀ descriptor,
      frame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (contextAt : frame.typing.module.contexts[target]? = some calleeContext)
    (calleeAt : frame.typing.module.impls[calleeContext.impl]? = some callee)
    (results : callee.results = #[⟨ty, .register, none⟩])
    (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (requests : frame.typing.resultRequests = [.register])
    (available : ∀ result after, rpBlockValue frame.source [] ⟨scope, statements, some (.call target [] origin)⟩ frame.rootCursor =
      .ok (result, after) → GlobalEffectsAvailable frame.interpretation frame.initialized after.eff)
    (inner : ∀ (caller : ConstructionSourceFrame) (after : ExecutionState) (currentTypes : RootTypes)
        (currentLive : Goose.Core.RootInst → Prop) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState),
      caller.interpretation.environment = { frame.interpretation.environment with
        scopes := (scope, state.nextScope) :: frame.interpretation.environment.scopes } →
      AcceptedWorld config caller.initialized after ambient currentTypes currentLive regions pending →
      AcceptedFrame config accepted caller after currentTypes →
      CheckedValue caller (.call target [] origin) ty roots typingAfter rootsAfter →
      ∃ nextTypes nextLive nextAmbient,
        let outcome := invokeCall fuel config caller.interpretation.environment target [] [.register ty] origin after
        RootTypesExtend currentTypes nextTypes ∧ after.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        after.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
        FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
        EarlierCallerObservations frontier after (Goose.Proofs.Exit.stepState outcome) currentTypes nextTypes ∧
        (match outcome with
         | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
         | .stop .. => True | .escape .. | .jump .. => False)) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := execActivationBody (fuel + 2) config frame.interpretation.environment []
        ⟨scope, statements, some (.call target [] origin)⟩ state
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations frontier state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  let activation := frame.interpretation.environment
  let child := entryStatementsFrame config frame state.nextScope
  have bodyScope : frame.source.impl.body.scope = scope := by simp [body, Block.scope]
  have bodyStatements : frame.source.impl.body.stmts = statements := by simp [body, Block.stmts]
  obtain ⟨scopeWorld, scopeSource, scopePosition⟩ := acceptedCalleeBodyScope config accepted frame context state ambient types live
    regions pending world source phase parameters scopes cursor
  rw [bodyScope] at scopeWorld scopeSource
  rw [bodyStatements] at scopePosition
  change AcceptedWorld config child.initialized (ownershipResultScopeState activation scope state) ambient types live regions pending at scopeWorld
  change AcceptedFrame config accepted child (ownershipResultScopeState activation scope state) types at scopeSource
  change SourcePosition accepted child (.statements statements) at scopePosition
  have childInterpretation : child.interpretation = frame.interpretation.enterScope scope state.nextScope := by
    simp [child, entryStatementsFrame, bodyScope]
  have childInitialized : child.initialized = frame.initialized := by simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame]
  have childPhase : child.phase = .implementation context := by simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame, phase]
  have childTyping : child.typing = { frame.typing with scope := scope } := by simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame, bodyScope]
  have childFuel : child.typingFuel = frame.typingFuel - 1 := by
    have fixed := congrArg (fun f : ConstructionSourceFrame => f.typingFuel) bodyFrame
    simp only [implementationBodyFrame] at fixed
    simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame, ← fixed]
  have depth : frame.typingFuel = 4096 := by
    have fixed := congrArg (fun f : ConstructionSourceFrame => f.typingFuel) bodyFrame
    simpa [implementationBodyFrame] using fixed.symm
  have childFuel' : child.typingFuel = 4095 := by simp [childFuel, depth]
  have childCounter : child.typingCounter = frame.typingCounter := by simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame]
  have childSource : child.source = { frame.source with scopes := scope :: frame.source.scopes } := by
    simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame, bodyScope]
  have childCursor : child.rootCursor = frame.rootCursor := by simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame]
  have childEnvironment : child.interpretation.environment =
      { activation with scopes := (scope, state.nextScope) :: activation.scopes } := by
    simp [childInterpretation, RootInterpretation.enterScope, activation]
  obtain ⟨middleRoots, tailRoots, lastRoots, rootedStatements, rootedTail, middleAvailable, tailAvailable⟩ :=
    position.blockTail_effects accepted frame scope statements (.call target [] origin) available
  have seqAvailable : ∀ rootsAfter, rpStmts child.source statements child.rootCursor = .ok ((), rootsAfter) →
      GlobalEffectsAvailable child.interpretation child.initialized rootsAfter.eff := by
    intro rootsAfter rooted
    have same : rootsAfter = middleRoots := by
      rw [childSource, childCursor] at rooted
      exact (Prod.mk.inj (Except.ok.inj (rooted.symm.trans rootedStatements))).2
    subst rootsAfter
    simpa [childInterpretation, RootInterpretation.enterScope, childInitialized, GlobalEffectsAvailable] using middleAvailable
  have childScalar : ∀ id expression origin, .letS id expression origin ∈ statements → ∀ descriptor,
      child.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
    intro id expression origin member descriptor declared
    apply scalar id expression origin member descriptor
    simpa [childSource] using declared
  obtain ⟨final, finalTypes, finalLive, sameInitialized, extend, finalActClock, finalScopeClock, finalWorld, finalSource, finalObserved, finalFlow⟩ :=
    execStmts_scalarLocal_prefix_observed form frontier (fuel + 1) config accepted child context
      (ownershipResultScopeState activation scope state) ambient types live regions pending
      (by simpa [childEnvironment, activation] using frontierBound) scopeWorld scopeSource childPhase scopePosition seqAvailable childScalar
  have entered := EarlierCallerObservations.enterScope frontier activation scope state types
  cases execution : execStmts (fuel + 1) config child.interpretation.environment statements
      (ownershipResultScopeState activation scope state) with
  | stop reason after =>
    simp only [execution, Goose.Proofs.Exit.stepState] at finalActClock finalScopeClock finalWorld finalSource finalObserved finalFlow
    have stopped : execActivationBody (fuel + 2) config activation [] ⟨scope, statements, some (.call target [] origin)⟩ state = .stop reason after := by
      apply execActivationBody_register_statements_stopped
      simpa [childEnvironment] using execution
    rw [stopped]
    have actBound : state.nextAct ≤ after.nextAct := by rw [finalActClock]; exact Nat.le_refl _
    have scopeBound : state.nextScope ≤ after.nextScope := by rw [finalScopeClock]; exact Nat.le_succ _
    exact ⟨finalTypes, finalLive, ambient, extend, actBound, scopeBound, sameInitialized ▸ finalWorld,
      sameInitialized ▸ finalSource.futureGlobals, entered.trans (Nat.le_refl _) finalObserved, trivial⟩
  | escape address carriers after | jump destination kind after => simp [execution] at finalFlow
  | ok flow after =>
    simp only [execution, Goose.Proofs.Exit.stepState] at finalActClock finalScopeClock finalWorld finalSource finalObserved finalFlow
    obtain ⟨normal, _, replay⟩ := finalFlow
    subst flow
    have finalAvailable : ∀ roots afterRoots, rpExpr final.source (.call target [] origin) final.rootCursor = .ok (roots, afterRoots) →
        GlobalEffectsAvailable final.interpretation final.initialized afterRoots.eff := by
      intro roots afterRoots rooted
      obtain ⟨_, rootedReplay, sourceSame, interpretationSame⟩ := replay
      rw [sourceSame, childSource] at rooted
      have sameMiddle : final.rootCursor = middleRoots := by
        rw [childSource, childCursor] at rootedReplay
        exact (Prod.mk.inj (Except.ok.inj (rootedReplay.symm.trans rootedStatements))).2
      rw [sameMiddle] at rooted
      have sameAfter : afterRoots = lastRoots := (Prod.mk.inj (Except.ok.inj (rooted.symm.trans rootedTail))).2
      subst afterRoots
      simpa [interpretationSame, childInterpretation, RootInterpretation.enterScope, childInitialized, sameInitialized, GlobalEffectsAvailable] using tailAvailable
    obtain ⟨roots, typingAfter, rootsAfter, checked⟩ := replay.registerCall_tail_checked accepted frame child final scope 4094 target origin statements
      calleeContext callee ty position (by simp [depth]) childTyping (by simpa using childFuel') childCounter childSource childCursor
      form contextAt calleeAt results scalarTy requests finalAvailable
    have tailSource := finalSource.withTypingFuel 4095
    have finalEnvironment : final.interpretation.environment =
        { activation with scopes := (scope, state.nextScope) :: activation.scopes } := by
      exact congrArg RootInterpretation.environment replay.2.2.2 |>.trans childEnvironment
    have normalRun : execStmts (fuel + 1) config
        { activation with scopes := (scope, state.nextScope) :: activation.scopes } statements
        (ownershipResultScopeState activation scope state) = .ok (.normal .unit) after := by
      simpa [← childEnvironment] using execution
    have actBound : state.nextAct ≤ after.nextAct := by rw [finalActClock]; exact Nat.le_refl _
    have scopeBound : state.nextScope ≤ after.nextScope := by rw [finalScopeClock]; exact Nat.le_succ _
    obtain ⟨nextTypes, nextLive, nextAmbient, nextExtend, acts, scopes, callWorld, clear, callObserved, result⟩ :=
      inner { final with typingFuel := 4095 } after finalTypes finalLive roots typingAfter rootsAfter finalEnvironment finalWorld tailSource checked
    simp only [finalEnvironment] at acts scopes callWorld clear callObserved result
    rw [sameInitialized, childInitialized] at callWorld clear
    have observedTail := execActivationBody_registerCall_earlierObservations fuel config activation scope statements ty target origin state after
      frontier finalTypes nextTypes frontierBound channels normalRun callObserved
    have allObserved := (entered.trans (Nat.le_refl _) finalObserved).trans (Nat.le_refl _) observedTail
    have bodyRun := execActivationBody_register_call_tail fuel config activation scope statements state after ty target origin channels normalRun
    cases execution : invokeCall fuel config
        { activation with scopes := (scope, state.nextScope) :: activation.scopes } target [] [.register ty] origin after with
    | stop reason stopped =>
      simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes callWorld clear result
      rw [bodyRun, execution] at allObserved ⊢
      exact ⟨nextTypes, nextLive, nextAmbient, (fun root ty found => nextExtend root ty (extend root ty found)),
        Nat.le_trans actBound acts, Nat.le_trans scopeBound scopes, callWorld, clear, allObserved, trivial⟩
    | escape address carriers stopped | jump destination kind stopped => simp [execution] at result
    | ok carriers stopped =>
      simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes callWorld clear result
      obtain ⟨ambientEq, value, rfl, represented⟩ := result
      subst nextAmbient
      have released := callWorld.releaseScope config frame.initialized stopped ambient nextTypes nextLive regions pending
        activation scope state.nextScope
      rw [bodyRun, execution] at allObserved ⊢
      exact ⟨nextTypes, _, ambient, (fun root ty found => nextExtend root ty (extend root ty found)),
        Nat.le_trans actBound acts, Nat.le_trans scopeBound scopes, released,
        clear.releaseScope activation scope state.nextScope, allObserved, rfl, value, rfl, represented⟩

#print axioms execActivationBody_scalarLocal_registerCall_earlier
#print axioms execActivationBody_registerCall_earlierObservations
end Goose.Proofs.ConstructionAcceptedExecution

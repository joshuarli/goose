import Goose.Proofs.ConstructionAcceptedRegisterCallTail

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem typeStatements_scalarLocal_callContext {statements : List Stmt} (form : ScalarLocalStatements statements) :
    ∀ (fuel : Nat) (environment next : TypingEnv) (before after : Nat),
      typeStatements fuel environment statements before = .ok (next, after) →
      next.module = environment.module ∧ next.resultRequests = environment.resultRequests := by
  induction form with
  | nil =>
    intro fuel environment next before after checked
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at checked; cases checked
    | succ fuel =>
      simp only [typeStatements, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at checked
      obtain ⟨rfl, rfl⟩ := checked
      exact ⟨rfl, rfl⟩
  | cons id expression origin rest form tail ih =>
    intro fuel environment next before after checked
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at checked; cases checked
    | succ fuel =>
      simp only [typeStatements, bind, StateT.bind] at checked
      cases step : typeStatement fuel environment (.letS id expression origin) before with
      | error failure => simp only [step, Except.bind] at checked; cases checked
      | ok pair =>
        obtain ⟨middle, counter⟩ := pair
        simp only [step, Except.bind] at checked
        cases fuel with
        | zero => change Except.error _ = Except.ok _ at step; cases step
        | succ fuel =>
          have middleShape := typeStatement_let_environment fuel environment middle id expression origin before counter step
          have preserved := ih (fuel + 1) middle next counter after checked
          simpa [middleShape] using preserved

theorem ScalarLocalReplay.registerCall_withArguments_tail_checked {config : EvalConfig} (accepted : AcceptedModule config)
    (blockFrame child final : ConstructionSourceFrame) (scope fuel target origin : Nat) (statements : List Stmt)
    (context : Context) (callee : Impl) (arguments : List Arg) (ty : Ty)
    (position : SourcePosition accepted blockFrame (.block ⟨scope, statements, some (.call target arguments origin)⟩))
    (nesting : blockFrame.typingFuel = (fuel + 1) + 1)
    (childTyping : child.typing = { blockFrame.typing with scope := scope })
    (childFuel : child.typingFuel = fuel + 1) (childCounter : child.typingCounter = blockFrame.typingCounter)
    (childSource : child.source = { blockFrame.source with scopes := scope :: blockFrame.source.scopes })
    (childCursor : child.rootCursor = blockFrame.rootCursor)
    (replay : ScalarLocalReplay child final statements) (form : ScalarLocalStatements statements)
    (contextAt : blockFrame.typing.module.contexts[target]? = some context)
    (calleeAt : blockFrame.typing.module.impls[context.impl]? = some callee)
    (results : callee.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (requests : blockFrame.typing.resultRequests = [.register])
    (available : ∀ roots rootsAfter,
      rpExpr final.source (.call target arguments origin) final.rootCursor = .ok (roots, rootsAfter) →
      GlobalEffectsAvailable final.interpretation final.initialized rootsAfter.eff) :
    ∃ roots typingAfter rootsAfter,
      CheckedValue { final with typingFuel := fuel + 1 } (.call target arguments origin) ty roots typingAfter rootsAfter := by
  obtain ⟨next, typingMiddle, rootMiddle, types, typingAfter, roots, rootsAfter,
    _, typedStatements, rootedStatements, typedTail, rootedTail⟩ :=
    position.blockTail_checks accepted blockFrame scope (fuel + 1) statements (.call target arguments origin) nesting
  obtain ⟨typedReplay, rootedReplay, sourceSame, interpretationSame⟩ := replay
  rw [childTyping, childFuel, childCounter] at typedReplay
  have sameTyping : (final.typing, final.typingCounter) = (next, typingMiddle) :=
    Except.ok.inj (typedReplay.symm.trans typedStatements)
  obtain ⟨sameEnvironment, sameCounter⟩ := Prod.mk.inj sameTyping
  rw [childSource, childCursor] at rootedReplay
  have sameRoots : final.rootCursor = rootMiddle :=
    (Prod.mk.inj (Except.ok.inj (rootedReplay.symm.trans rootedStatements))).2
  have finalRooted : rpExpr final.source (.call target arguments origin) final.rootCursor = .ok (roots, rootsAfter) := by
    rw [sourceSame, childSource, sameRoots]
    exact rootedTail
  obtain ⟨sameModule, sameRequests⟩ := typeStatements_scalarLocal_callContext form (fuel + 1)
    { blockFrame.typing with scope := scope } next blockFrame.typingCounter typingMiddle typedStatements
  have singleton := typeExpr_registerCall_tail_result fuel next target origin context callee arguments ty typingMiddle typingAfter types
    (by simpa [sameModule] using contextAt) (by simpa [sameModule] using calleeAt) results scalar
    (by simpa [sameRequests] using requests) typedTail
  subst types
  refine ⟨roots, typingAfter, rootsAfter, ?_, finalRooted, available roots rootsAfter finalRooted⟩
  simpa [sameEnvironment, sameCounter] using typedTail


theorem ScalarLocalReplay.registerCall_tail_checked {config : EvalConfig} (accepted : AcceptedModule config)
    (blockFrame child final : ConstructionSourceFrame) (scope fuel target origin : Nat) (statements : List Stmt)
    (context : Context) (callee : Impl) (ty : Ty)
    (position : SourcePosition accepted blockFrame (.block ⟨scope, statements, some (.call target [] origin)⟩))
    (nesting : blockFrame.typingFuel = (fuel + 1) + 1)
    (childTyping : child.typing = { blockFrame.typing with scope := scope })
    (childFuel : child.typingFuel = fuel + 1) (childCounter : child.typingCounter = blockFrame.typingCounter)
    (childSource : child.source = { blockFrame.source with scopes := scope :: blockFrame.source.scopes })
    (childCursor : child.rootCursor = blockFrame.rootCursor)
    (replay : ScalarLocalReplay child final statements) (form : ScalarLocalStatements statements)
    (contextAt : blockFrame.typing.module.contexts[target]? = some context)
    (calleeAt : blockFrame.typing.module.impls[context.impl]? = some callee)
    (results : callee.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (requests : blockFrame.typing.resultRequests = [.register])
    (available : ∀ roots rootsAfter,
      rpExpr final.source (.call target [] origin) final.rootCursor = .ok (roots, rootsAfter) →
      GlobalEffectsAvailable final.interpretation final.initialized rootsAfter.eff) :
    ∃ roots typingAfter rootsAfter,
      CheckedValue { final with typingFuel := fuel + 1 } (.call target [] origin) ty roots typingAfter rootsAfter := by
  exact ScalarLocalReplay.registerCall_withArguments_tail_checked accepted blockFrame child final scope fuel target origin statements
    context callee [] ty position nesting childTyping childFuel childCounter childSource childCursor replay form contextAt calleeAt
    results scalar requests available

theorem execActivationBody_registerCall_afterStatements (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt) (ty : Ty) (target origin : Nat)
    (before middle : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (channels : activation.channels = [.register ty])
    (normal : execStmts (fuel + 1) config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements
      (ownershipResultScopeState activation scope before) = .ok (.normal .unit) middle)
    (middleActs : before.nextAct ≤ middle.nextAct) (middleScopes : before.nextScope ≤ middle.nextScope)
    (inner : ∃ nextTypes nextLive nextAmbient,
      let environment := { activation with scopes := (scope, before.nextScope) :: activation.scopes }
      let outcome := invokeCall fuel config environment target [] [.register ty] origin middle
      RootTypesExtend types nextTypes ∧ middle.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      middle.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False)) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := execActivationBody (fuel + 2) config activation [] ⟨scope, statements, some (.call target [] origin)⟩ before
      RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  let environment := { activation with scopes := (scope, before.nextScope) :: activation.scopes }
  have body := execActivationBody_register_call_tail fuel config activation scope statements before middle ty target origin channels normal
  obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, world, clear, result⟩ := inner
  cases execution : invokeCall fuel config environment target [] [.register ty] origin middle with
  | stop reason after =>
    simp only [environment] at execution
    simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes world clear result
    rw [body, execution]
    exact ⟨nextTypes, nextLive, nextAmbient, extend, Nat.le_trans middleActs acts, Nat.le_trans middleScopes scopes, world, clear, trivial⟩
  | escape address carriers after | jump destination kind after =>
    simp only [environment] at execution
    simp [execution] at result
  | ok carriers after =>
    simp only [environment] at execution
    simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes world clear result
    obtain ⟨rfl, value, rfl, represented⟩ := result
    rw [body, execution]
    have released := world.releaseScope config initialized after nextAmbient nextTypes nextLive regions pending
      activation scope before.nextScope
    exact ⟨nextTypes, _, nextAmbient, extend, Nat.le_trans middleActs acts, Nat.le_trans middleScopes scopes, released,
      clear.releaseScope activation scope before.nextScope, rfl, value, rfl, represented⟩

theorem execActivationBody_scalarLocal_registerCall_compose (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context : Nat) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (scope : Nat) (statements : List Stmt) (target origin : Nat) (calleeContext : Context) (callee : Impl) (ty : Ty)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation context)
    (parameters : frame.source.impl.params = #[]) (scopes : frame.interpretation.environment.scopes = [])
    (cursor : frame.rootCursor = ⟨0, {}, []⟩) (bodyFrame : implementationBodyFrame config frame = frame)
    (body : frame.source.impl.body = ⟨scope, statements, some (.call target [] origin)⟩)
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
      AcceptedWorld config caller.initialized after ambient currentTypes currentLive regions pending →
      AcceptedFrame config accepted caller after currentTypes →
      CheckedValue caller (.call target [] origin) ty roots typingAfter rootsAfter →
      ∃ nextTypes nextLive nextAmbient,
        let outcome := invokeCall fuel config caller.interpretation.environment target [] [.register ty] origin after
        RootTypesExtend currentTypes nextTypes ∧ after.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        after.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
        FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
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
  obtain ⟨final, finalTypes, finalLive, sameInitialized, extend, finalActClock, finalScopeClock, finalWorld, finalSource, finalFlow⟩ :=
    execStmts_scalarLocal_prefix form (fuel + 1) config accepted child context (ownershipResultScopeState activation scope state)
      ambient types live regions pending scopeWorld scopeSource childPhase scopePosition seqAvailable childScalar
  cases execution : execStmts (fuel + 1) config child.interpretation.environment statements
      (ownershipResultScopeState activation scope state) with
  | stop reason after =>
    simp only [execution, Goose.Proofs.Exit.stepState] at finalActClock finalScopeClock finalWorld finalSource finalFlow
    have stopped : execActivationBody (fuel + 2) config activation [] ⟨scope, statements, some (.call target [] origin)⟩ state = .stop reason after := by
      apply execActivationBody_register_statements_stopped
      simpa [childEnvironment] using execution
    rw [stopped]
    have actBound : state.nextAct ≤ after.nextAct := by rw [finalActClock]; exact Nat.le_refl _
    have scopeBound : state.nextScope ≤ after.nextScope := by rw [finalScopeClock]; exact Nat.le_succ _
    exact ⟨finalTypes, finalLive, ambient, extend, actBound, scopeBound, sameInitialized ▸ finalWorld,
      sameInitialized ▸ finalSource.futureGlobals, trivial⟩
  | escape address carriers after | jump destination kind after => simp [execution] at finalFlow
  | ok flow after =>
    simp only [execution, Goose.Proofs.Exit.stepState] at finalActClock finalScopeClock finalWorld finalSource finalFlow
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
    have callSafe := inner { final with typingFuel := 4095 } after finalTypes finalLive roots typingAfter rootsAfter finalWorld tailSource checked
    have innerSafe : ∃ nextTypes nextLive nextAmbient,
      let outcome := invokeCall fuel config
        { activation with scopes := (scope, state.nextScope) :: activation.scopes } target [] [.register ty] origin after
      RootTypesExtend finalTypes nextTypes ∧ after.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      after.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
      simpa only [finalEnvironment, sameInitialized, childInitialized] using callSafe
    obtain ⟨nextTypes, nextLive, nextAmbient, nextExtend, acts, scopes, finalWorld', clear, result⟩ :=
      execActivationBody_registerCall_afterStatements fuel config frame.initialized activation scope statements ty target origin state after
        ambient finalTypes regions pending channels normalRun actBound scopeBound innerSafe
    exact ⟨nextTypes, nextLive, nextAmbient, (fun root ty found => nextExtend root ty (extend root ty found)), acts, scopes,
      finalWorld', clear, result⟩

#print axioms execActivationBody_scalarLocal_registerCall_compose
#print axioms execActivationBody_registerCall_afterStatements
#print axioms ScalarLocalReplay.registerCall_withArguments_tail_checked
#print axioms ScalarLocalReplay.registerCall_tail_checked
#print axioms typeStatements_scalarLocal_callContext
end Goose.Proofs.ConstructionAcceptedExecution

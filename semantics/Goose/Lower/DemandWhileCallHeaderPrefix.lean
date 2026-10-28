import Goose.Lower.DemandWhileCallCursor
import Goose.Lower.DemandWhileScalarCallTrueBody
import Goose.Lower.DemandWhileHeaderPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_while_scalar_call_header_prefix_complete {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {initialState state : St} {count : Nat}
    (iterations : WhileIterations cfg env condition body count initialState state)
    (source : StmtSource cfg env (.while condition body origin) state)
    (original : StmtSource cfg env (.while condition body origin) initialState) (world : source.world = original.world)
    (fragment : ∀ middle : St, ReachableScalarCallStatements cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } body.stmts)
    (noValue : body.value = none)
    {cx : FnCtx} {results : List Ty} {loop : Option LoopCtx} {root : DemandNode} {owner : Nat}
    (targetConfig : cx.cfg = ⟨cfg.profile, lower cfg.mod⟩)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context) {before headerState built : LS}
    {header : BlockId} {frame : GIR.Frame}
    (headerInput : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv headerState frame (header, 0))
    (headerTarget : ∃ block, cx.fn.blocks[header]? = some block ∧ block.params = [])
    (headerId : header = (newBlock [] (lowerEnv cfg.mod env.vars results) before).1.1)
    (headerEq : headerState = demandWhileHeaderBefore (lowerEnv cfg.mod env.vars results) before)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.while condition body origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded headerState.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨(header, 0), frame, state⟩)
    (family : GeneratedExpressionPrefixFamily cx results selected loop condition (@GeneratedControlProgressCursor cfg env cx))
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) headerState = ((), built)) (extended : ExtT built cx.fn.blocks)
    (headerReach : Evidence.RuntimePoint cx.cfg cx.fn (header, 0) frame state)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨(header, 0), frame, state⟩ reached)
    :
    WhileCallHeaderCursor cx.fn results selected original before built frame (header, 0) map required reached ∨
    ∃ (sourceFuel consumed remaining : Nat) (boundary : DemandRuntimePoint),
      consumed + remaining = taken ∧ DemandRuntimePrefix cx consumed ⟨(header, 0), frame, state⟩ boundary ∧
      DemandRuntimePrefix cx remaining boundary reached ∧
      execStmt sourceFuel cfg env (.while condition body origin) initialState = .ok (.normal .unit) boundary.state ∧
      Post cfg env cx headerState frame built boundary.frame boundary.point [] ∧
      map.Bounded built.vals.size ∧ map.Realizes cfg.mod original.world env boundary := by
  cases cx with
  | mk current caller =>
    change current = ⟨cfg.profile, lower cfg.mod⟩ at targetConfig
    subst current
    let cx : FnCtx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩
    obtain ⟨child, childType, canonical, childOwner, childAdmitted, childRealized, childInput, childExtended, childOccurrence, childRows⟩ :=
      accepted_generated_while_header_condition source selected owned occurrence rows admitted realized headerInput headerEq lowered extended
    have progress := (family child childOwner childOccurrence childRows coverage childAdmitted bounded childRealized childInput childExtended steps).progress
    cases progress with
    | interior cursor => exact Or.inl (.existing (.condition iterations source world child canonical cursor.demanded cursor.progress))
    | @complete fuel consumed remaining current value split executed residual evaluated boundary =>
      have typed := (child.result fuel value evaluated).typed
      rw [childType] at typed
      obtain ⟨boolean, rfl⟩ := hasTy_bool typed
      rcases residual.uncons with ⟨zero, rfl⟩ | ⟨rest, nextPoint, restCount, first, suffix⟩
      · obtain ⟨bodyBlock, exitBlock, forked, bodyStart, bodyEnd, jumped, value, forkRun, bodyEq, bodyRun,
          jumpRun, finalEq, forkExtended, bodyExtended, jumpExtended, exitPoint, exitStack, exitVals⟩ :=
          generated_while_exit_builder lowered boundary.post.pp extended
        have cell := boundary.post.has ((lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1,
          .val (.bool boolean)) (by simp)
        have step : ∃ next, ∀ targetFuel, DemandInstructionStep cx targetFuel reached next := by
          refine ⟨⟨(if boolean then bodyBlock else exitBlock, 0), reached.frame, reached.state⟩, ?_⟩
          intro targetFuel
          exact generated_if_branch_step boolean forkRun boundary.post.pp forkExtended cell targetFuel
        exact Or.inl (.existing (.fork iterations source world child boolean fuel canonical evaluated boundary step))
      · cases boolean with
        | false =>
          obtain ⟨exitBlock, exitStep, _, finalPost, finalBounded, finalRealized⟩ :=
            accepted_generated_while_false_exit source child canonical evaluated boundary lowered extended
          obtain ⟨stepFuel, actual⟩ := runtimeStep_demandInstructionStep first
          have equal := actual.deterministic (exitStep stepFuel)
          have nextEq : nextPoint = ⟨(exitBlock, 0), current.frame, current.state⟩ := by cases nextPoint; exact equal
          subst nextPoint
          obtain ⟨sourceFuel, sourceDone⟩ := while_iterations_condition_false (origin := origin) iterations evaluated
          have originalRealized : map.Realizes cfg.mod original.world env ⟨(exitBlock, 0), current.frame, current.state⟩ := by
            simpa only [world] using finalRealized
          exact Or.inr ⟨sourceFuel, consumed + 1, rest, _, by omega, executed.append (.next first (.zero _)),
            suffix, sourceDone, finalPost, finalBounded, originalRealized⟩
        | true =>
          obtain ⟨bodyBlock, exitBlock, forked, bodyStart, bodyEnd, jumped, value, branch, canonicalBranch,
            forkRun, bodyEq, bodyRun, jumpRun, jumpExtended, branchStep, bodyPrefix, bodyStopped⟩ :=
            accepted_generated_while_scalar_call_true_body source child canonical evaluated (fragment current.state) noValue rfl selected owned
              headerInput headerTarget headerId headerEq occurrence rows coverage admitted boundary (executed.reachable headerReach) lowered extended
          obtain ⟨stepFuel, actual⟩ := runtimeStep_demandInstructionStep first
          have equal := actual.deterministic (branchStep stepFuel)
          have nextEq : nextPoint = ⟨(bodyBlock, 0), current.frame, current.state⟩ := by cases nextPoint; exact equal
          subst nextPoint
          have bodyProgress := bodyPrefix suffix
          cases bodyProgress.progress with
          | interior demanded => exact Or.inl (.scalarBody iterations source world child fuel canonical evaluated branch canonicalBranch demanded)
          | @complete bodyFuel bodyConsumed bodyRest bodyPoint flow bodyCount bodySteps bodyResidual bodyDone ended =>
            have normal := ended.normal
            subst flow
            have forkExtended : ExtT forked cx.fn.blocks := by
              have bodyExtended := jumpExtended.of_adv (adv_emitTerm jumpRun)
              have startExtended := bodyExtended.of_adv (advB_lowerBlock _ [] false body _ _ _ _ bodyRun)
              rw [bodyEq] at startExtended
              exact startExtended
            have reentryPost := generated_while_reentry_post branch headerInput.atPoint headerInput.related boundary.post
              forkRun forkExtended bodyEq bodyRun ended
            obtain ⟨next, typing, roots, nextWorld, observation, plans, path, context, nextInput, nextBounded, nextRealized, back⟩ :=
              accepted_generated_while_reentry source branch canonicalBranch evaluated bodyDone headerInput headerTarget bounded
                bodyRun jumpRun jumpExtended ended (outerPost := by cases loop <;> simp_all)
            rcases bodyResidual.uncons with ⟨zero, rfl⟩ | ⟨tail, afterBack, tailCount, backStep, backResidual⟩
            · exact Or.inl (.existing (.backEdge iterations source world child fuel bodyFuel canonical evaluated branch canonicalBranch bodyDone ended back))
            · obtain ⟨backFuel, actualBack⟩ := runtimeStep_demandInstructionStep backStep
              have equalBack := actualBack.deterministic (back backFuel)
              have afterEq : afterBack = ⟨(header, 0), bodyPoint.frame, bodyPoint.state⟩ := by cases afterBack; exact equalBack
              subst afterBack
              obtain ⟨nextOwned, nextAdmitted, nextOccurrence, nextRows⟩ :=
                generated_while_reentry_context source next roots plans path context selected owned occurrence rows admitted
              have iteration := WhileIterations.next evaluated bodyDone (Or.inl ⟨.unit, rfl⟩) (WhileIterations.zero bodyPoint.state)
              have allIterations : WhileIterations cfg env condition body (count + 1) initialState bodyPoint.state := by
                simpa using iterations.append iteration
              have nextProgress := accepted_generated_while_scalar_call_header_prefix_complete allIterations next original (nextWorld.trans world)
                fragment noValue rfl
                selected nextOwned nextInput headerTarget headerId headerEq nextOccurrence nextRows coverage nextAdmitted
                nextBounded nextRealized family lowered extended
                (((executed.append (.next first bodySteps)).append (.next backStep (.zero _))).reachable headerReach) backResidual
              rcases nextProgress with demanded | ⟨sourceFuel, laterConsumed, laterRest, final, laterCount,
                laterSteps, laterSuffix, sourceDone, finalPost, finalBounded, finalRealized⟩
              · exact Or.inl demanded.rebase
              · exact Or.inr ⟨sourceFuel, consumed + (bodyConsumed + 1) + 1 + laterConsumed, laterRest, final, by omega,
                  ((executed.append (.next first bodySteps)).append (.next backStep (.zero _))).append laterSteps,
                  laterSuffix, sourceDone, reentryPost.comp finalPost, finalBounded, finalRealized⟩

termination_by taken
decreasing_by omega



theorem accepted_generated_while_call_header_prefix_complete {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {initialState state : St} {count : Nat}
    (iterations : WhileIterations cfg env condition body count initialState state)
    (source : StmtSource cfg env (.while condition body origin) state)
    (original : StmtSource cfg env (.while condition body origin) initialState) (world : source.world = original.world)
    {callContext : ContextId} {arguments : List Arg} {callOrigin statementOrigin : OriginId}
    (bodyStatements : body.stmts = [.expr (.call callContext arguments callOrigin) statementOrigin]) (noValue : body.value = none)
    {calleeContext : Context} {callee : Impl} (contextAt : cfg.mod.contexts[callContext]? = some calleeContext)
    (implAt : cfg.mod.impls[calleeContext.impl]? = some callee) (depth : env.depth < maxCallDepth)
    (fragment : ∀ current : St, WhileMixedStatements cfg
      { vars := callee.vars, act := current.nextAct, scopes := (callee.body.scope, current.nextScope) :: [], depth := env.depth + 1 } callee.body.stmts)
    {expression : Expr} (form : ControlPrefixExpression expression) (hasValue : callee.body.value = some expression)
    (shrink : cfg.mod.profile = .shrink)
    (argumentsForm : ∀ (middle : St) {innerState : St} (argumentSource : StmtSource cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } (.expr (.call callContext arguments callOrigin) statementOrigin) innerState),
      CallMixedArguments argumentSource.rootsEnv.access arguments)
    (stoppedArgumentsForm : ∀ (middle : St) {innerState : St} (argumentSource : StmtSource cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } (.expr (.call callContext arguments callOrigin) statementOrigin) innerState),
      CallMixedStoppedArguments argumentSource.rootsEnv.access arguments)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (targetConfig : cx.cfg = ⟨cfg.profile, lower cfg.mod⟩)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context) {before headerState built : LS}
    {header : BlockId} {frame : GIR.Frame}
    (headerInput : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv headerState frame (header, 0))
    (headerTarget : ∃ block, cx.fn.blocks[header]? = some block ∧ block.params = [])
    (headerId : header = (newBlock [] (lowerEnv cfg.mod env.vars results) before).1.1)
    (headerEq : headerState = demandWhileHeaderBefore (lowerEnv cfg.mod env.vars results) before)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement none (.while condition body origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded headerState.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨(header, 0), frame, state⟩)
    (family : GeneratedExpressionPrefixFamily cx results selected none condition (@GeneratedControlProgressCursor cfg env cx))
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) headerState = ((), built)) (extended : ExtT built cx.fn.blocks)
    (headerReach : Evidence.RuntimePoint cx.cfg cx.fn (header, 0) frame state)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨(header, 0), frame, state⟩ reached)
    :
    WhileCallHeaderCursor cx.fn results selected original before built frame (header, 0) map required reached ∨
    ∃ (sourceFuel consumed remaining : Nat) (boundary : DemandRuntimePoint),
      consumed + remaining = taken ∧ DemandRuntimePrefix cx consumed ⟨(header, 0), frame, state⟩ boundary ∧
      DemandRuntimePrefix cx remaining boundary reached ∧
      execStmt sourceFuel cfg env (.while condition body origin) initialState = .ok (.normal .unit) boundary.state ∧
      Post cfg env cx headerState frame built boundary.frame boundary.point [] ∧
      map.Bounded built.vals.size ∧ map.Realizes cfg.mod original.world env boundary := by
  have mixed : ∀ middle : St, ReachableScalarCallStatements cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } body.stmts := by
    intro middle
    rw [bodyStatements]
    exact ReachableScalarCallStatements.single contextAt implAt depth fragment form hasValue shrink
      (argumentsForm middle) (stoppedArgumentsForm middle)
  exact accepted_generated_while_scalar_call_header_prefix_complete iterations source original world mixed noValue targetConfig
    selected owned headerInput headerTarget headerId headerEq occurrence rows coverage admitted bounded realized family lowered extended headerReach steps

#print axioms accepted_generated_while_call_header_prefix_complete
#print axioms accepted_generated_while_scalar_call_header_prefix_complete
end Goose.Lower

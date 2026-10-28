import Goose.Lower.DemandWhileCallTrueStopped
import Goose.Lower.DemandWhileHeaderStopped

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_while_call_header_stopped_complete {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {initialState state : St} {count : Nat}
    (iterations : WhileIterations cfg env condition body count initialState state)
    (source : StmtSource cfg env (.while condition body origin) state)
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
    (family : GeneratedStoppedExpressionPrefixFamily cx results selected none condition)
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) headerState = ((), built)) (extended : ExtT built cx.fn.blocks)
    (headerReach : Evidence.RuntimePoint cx.cfg cx.fn (header, 0) frame state)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨(header, 0), frame, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    (∃ sourceFuel, execStmt sourceFuel cfg env (.while condition body origin) initialState = .stop stop after) ∨
    ∃ (sourceFuel consumed remaining : Nat) (boundary : DemandRuntimePoint),
      consumed + remaining = taken ∧ DemandRuntimePrefix cx consumed ⟨(header, 0), frame, state⟩ boundary ∧
      DemandRuntimePrefix cx remaining boundary reached ∧
      execStmt sourceFuel cfg env (.while condition body origin) initialState = .ok (.normal .unit) boundary.state ∧
      Post cfg env cx headerState frame built boundary.frame boundary.point [] ∧
      map.Bounded built.vals.size ∧ map.Realizes cfg.mod source.world env boundary := by
  obtain ⟨child, childType, canonical, progress⟩ :=
    accepted_generated_while_header_stopped source selected owned occurrence rows admitted realized headerInput headerEq coverage bounded
      family lowered extended steps stopped nonTimeout
  rcases accepted_generated_while_condition_stopped_outcome iterations child progress nonTimeout with
    stoppedSource | ⟨fuel, consumed, remaining, current, value, split, executed, residual, evaluated, boundary⟩
  · exact Or.inl stoppedSource
  · have typed := (child.result fuel value evaluated).typed
    rw [childType] at typed
    obtain ⟨boolean, rfl⟩ := hasTy_bool typed
    cases boolean with
    | false =>
      obtain ⟨exitBlock, exitStep, _, finalPost, finalBounded, finalRealized⟩ :=
        accepted_generated_while_false_exit source child canonical evaluated boundary lowered extended
      rcases residual.uncons with ⟨zero, rfl⟩ | ⟨rest, nextPoint, restCount, first, suffix⟩
      · exact (stopped.excludes_step_nonTimeout nonTimeout (exitStep targetFuel)).elim
      · obtain ⟨stepFuel, actual⟩ := runtimeStep_demandInstructionStep first
        have equal := actual.deterministic (exitStep stepFuel)
        have nextEq : nextPoint = ⟨(exitBlock, 0), current.frame, current.state⟩ := by cases nextPoint; exact equal
        subst nextPoint
        obtain ⟨sourceFuel, sourceDone⟩ := while_iterations_condition_false (origin := origin) iterations evaluated
        exact Or.inr ⟨sourceFuel, consumed + 1, rest, _, by omega, executed.append (.next first (.zero _)),
          suffix, sourceDone, finalPost, finalBounded, finalRealized⟩
    | true =>
      rcases accepted_generated_while_call_true_stopped iterations source child canonical evaluated bodyStatements noValue
        contextAt implAt depth fragment form hasValue shrink (argumentsForm current.state) (stoppedArgumentsForm current.state)
        targetConfig selected owned headerInput headerTarget headerId headerEq occurrence rows bounded coverage admitted boundary
        (executed.reachable headerReach) lowered extended
        residual stopped nonTimeout with stoppedSource | ⟨bodyConsumed, rest, nextPoint, next, allIterations, bodyCount,
          positive, bodySteps, suffix, typing, roots, world, observation, plans, path, context, nextInput, nextPost,
          nextBounded, nextRealized, pointEq, nextOwned, nextAdmitted, nextOccurrence, nextRows⟩
      · exact Or.inl stoppedSource
      · cases nextPoint with
        | mk nextPt nextFrame nextState =>
          simp only at pointEq
          subst nextPt
          have nextProgress := accepted_generated_while_call_header_stopped_complete allIterations next bodyStatements noValue
            contextAt implAt depth fragment form hasValue shrink argumentsForm stoppedArgumentsForm targetConfig selected nextOwned
            nextInput headerTarget headerId headerEq nextOccurrence nextRows coverage nextAdmitted nextBounded nextRealized
            family lowered extended ((executed.append bodySteps).reachable headerReach) suffix stopped nonTimeout
          rcases nextProgress with stoppedSource | ⟨sourceFuel, laterConsumed, laterRest, final, laterCount,
            laterSteps, laterSuffix, sourceDone, finalPost, finalBounded, finalRealized⟩
          · exact Or.inl stoppedSource
          · have combinedPost := nextPost.comp finalPost
            have originalRealized : map.Realizes cfg.mod source.world env final := by
              simpa only [world] using finalRealized
            exact Or.inr ⟨sourceFuel, consumed + bodyConsumed + laterConsumed, laterRest, final, by omega,
              (executed.append bodySteps).append laterSteps, laterSuffix, sourceDone, combinedPost, finalBounded, originalRealized⟩
termination_by taken
decreasing_by omega

#print axioms accepted_generated_while_call_header_stopped_complete
end Goose.Lower

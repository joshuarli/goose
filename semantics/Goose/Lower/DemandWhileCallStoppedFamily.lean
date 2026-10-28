import Goose.Lower.DemandWhileCallHeaderStopped
import Goose.Lower.DemandWhileCallPrefixFamily

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_while_scalar_call_stopped_family {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (condition : Expr) (body : Core.Block) (origin : OriginId)
    (fragment : ∀ middle : St, ReachableScalarCallStatements cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } body.stmts)
    (noValue : body.value = none)
    (family : GeneratedStoppedExpressionPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected none condition) :
    ReachableStoppedStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected none (.while condition body origin) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended callerStart taken reached steps targetFuel stop after stopped nonTimeout
  let cx : FnCtx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩
  have lowered : lowerStmt none (.while condition body origin) (lowerEnv cfg.mod env.vars results) before =
      ((), (lowerStmt none (.while condition body origin) (lowerEnv cfg.mod env.vars results) before).2) := by
    generalize run : lowerStmt none (.while condition body origin) (lowerEnv cfg.mod env.vars results) before = output
    cases output with
    | mk returned builder => cases returned; rfl
  obtain ⟨header, headerState, loopRun, headerId, headerEq, headerTarget, headerPost, headerGenerated, headerStep⟩ :=
    generated_while_header_entry lowered input.atPoint extended input.related input.generated
  have headerInput : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv headerState initial (header, 0) :=
    ⟨input.metadata, input.loops, headerPost.pp, headerPost.rel, input.moduleEq, input.resultsEq,
      input.depth, trivial, trivial, headerGenerated, trivial⟩
  have headerBounded := bounded.mono headerPost.mono
  have headerRealized : map.Realizes cfg.mod source.world env ⟨(header, 0), initial, state⟩ := by
    simpa only [RetainedSsaMap.Realizes] using realized
  rcases steps.uncons with ⟨zero, rfl⟩ | ⟨remaining, nextPoint, count, first, residual⟩
  · exact (stopped.excludes_step_nonTimeout nonTimeout (headerStep targetFuel)).elim
  · obtain ⟨stepFuel, actual⟩ := runtimeStep_demandInstructionStep first
    have equal := actual.deterministic (headerStep stepFuel)
    have nextEq : nextPoint = ⟨(header, 0), initial, state⟩ := by cases nextPoint; exact equal
    subst nextPoint
    rcases accepted_generated_while_scalar_call_header_stopped_complete (WhileIterations.zero state) source fragment noValue rfl selected owned
      headerInput headerTarget headerId headerEq occurrence rows coverage admitted headerBounded headerRealized family loopRun extended
      (Evidence.RuntimePoint.step callerStart first) residual stopped nonTimeout with stoppedSource | ⟨sourceFuel, consumed, rest, final, finalCount, executed, suffix,
        sourceDone, finalPost, finalBounded, finalRealized⟩
    · obtain ⟨sourceFuel, done⟩ := stoppedSource
      exact .aborted sourceFuel (by simp [bind_apply, done])
    · apply StoppedStatementPrefix.complete (flow := .normal .unit) (fuel := sourceFuel)
        (consumed := consumed + 1) (remaining := rest) (boundary := final)
      · omega
      · exact .next first executed
      · exact suffix
      · simp [bind_apply, sourceDone, prepareLoopFlow, prepareReturn, pure_apply]
      · exact .normal (headerPost.comp finalPost) (source.result sourceFuel _ sourceDone) finalBounded finalRealized


theorem accepted_generated_while_call_stopped_family {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (condition : Expr) (body : Core.Block) (origin : OriginId)
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
    (family : GeneratedStoppedExpressionPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected none condition) :
    ReachableStoppedStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected none (.while condition body origin) := by
  have mixed : ∀ middle : St, ReachableScalarCallStatements cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } body.stmts := by
    intro middle
    rw [bodyStatements]
    exact ReachableScalarCallStatements.single contextAt implAt depth fragment form hasValue shrink
      (argumentsForm middle) (stoppedArgumentsForm middle)
  intro state
  exact accepted_generated_while_scalar_call_stopped_family selected condition body origin mixed noValue family (state := state)

#print axioms accepted_generated_while_call_stopped_family
#print axioms accepted_generated_while_scalar_call_stopped_family
end Goose.Lower

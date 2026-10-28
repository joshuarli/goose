import Goose.Lower.DemandWhileCallHeaderPrefix
import Goose.Lower.DemandWhilePrefixFamily

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_while_scalar_call_prefix_family {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (condition : Expr) (body : Core.Block) (origin : OriginId)
    (fragment : ∀ middle : St, ReachableScalarCallStatements cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } body.stmts)
    (noValue : body.value = none)
    (family : GeneratedExpressionPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop condition (@GeneratedControlProgressCursor cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩)) :
    ReachableStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop (.while condition body origin)
      (@WhileCallStatementCursor cfg env caller results root owner selected) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended callerStart taken reached steps
  let cx : FnCtx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩
  refine ⟨owned, coverage, ?_⟩
  have lowered : lowerStmt loop (.while condition body origin) (lowerEnv cfg.mod env.vars results) before =
      ((), (lowerStmt loop (.while condition body origin) (lowerEnv cfg.mod env.vars results) before).2) := by
    generalize run : lowerStmt loop (.while condition body origin) (lowerEnv cfg.mod env.vars results) before = output
    cases output with
    | mk returned builder => cases returned; rfl
  obtain ⟨header, headerState, loopRun, headerId, headerEq, headerTarget, headerPost, headerGenerated, headerStep⟩ :=
    generated_while_header_entry lowered input.atPoint extended input.related input.generated
  have headerExtension : before.Ext headerState := by
    rw [headerEq]
    exact demandWhileHeaderBefore_ext _ _
  have headerInput : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv headerState initial (header, 0) := by
    cases loop with
    | none => exact ⟨input.metadata, input.loops, headerPost.pp, headerPost.rel, input.moduleEq, input.resultsEq,
        input.depth, trivial, trivial, headerGenerated, trivial⟩
    | some context => exact ⟨input.metadata, input.loops, headerPost.pp, headerPost.rel, input.moduleEq, input.resultsEq,
        input.depth, input.targets, input.counter.afterPost headerPost, headerGenerated, input.frames.mono headerExtension⟩
  have headerBounded := bounded.mono headerPost.mono
  have headerRealized : map.Realizes cfg.mod source.world env ⟨(header, 0), initial, state⟩ := by
    simpa only [RetainedSsaMap.Realizes] using realized
  rcases steps.uncons with ⟨zero, rfl⟩ | ⟨remaining, nextPoint, count, first, residual⟩
  · exact .interior (.entry realized ⟨⟨(header, 0), initial, state⟩, headerStep⟩)
  · obtain ⟨stepFuel, actual⟩ := runtimeStep_demandInstructionStep first
    have equal := actual.deterministic (headerStep stepFuel)
    have nextEq : nextPoint = ⟨(header, 0), initial, state⟩ := by cases nextPoint; exact equal
    subst nextPoint
    rcases accepted_generated_while_scalar_call_header_prefix_complete (WhileIterations.zero state) source source rfl fragment noValue rfl selected owned
      headerInput headerTarget headerId headerEq occurrence rows coverage admitted headerBounded headerRealized family loopRun extended
      (Evidence.RuntimePoint.step callerStart first) residual with demanded | ⟨sourceFuel, consumed, rest, final, finalCount, executed, suffix,
        sourceDone, finalPost, finalBounded, finalRealized⟩
    · exact .interior (.header demanded.rebase)
    · apply DemandPrefixDecomposition.complete (value := .normal .unit) (sourceFuel := sourceFuel)
        (consumed := consumed + 1) (remaining := rest) (boundary := final)
      · omega
      · exact .next first executed
      · exact suffix
      · cases loop <;> simp [bind_apply, sourceDone, prepareLoopFlow, prepareReturn, prepareLoopExit, pure_apply]
      · exact .normal (headerPost.comp finalPost) (source.result sourceFuel _ sourceDone) finalBounded finalRealized


theorem accepted_generated_while_call_prefix_family {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
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
    (family : GeneratedExpressionPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected none condition (@GeneratedControlProgressCursor cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩)) :
    ReachableStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected none (.while condition body origin)
      (@WhileCallStatementCursor cfg env caller results root owner selected) := by
  have mixed : ∀ middle : St, ReachableScalarCallStatements cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } body.stmts := by
    intro middle
    rw [bodyStatements]
    exact ReachableScalarCallStatements.single contextAt implAt depth fragment form hasValue shrink
      (argumentsForm middle) (stoppedArgumentsForm middle)
  intro state
  exact accepted_generated_while_scalar_call_prefix_family selected condition body origin mixed noValue family (state := state)

#print axioms accepted_generated_while_call_prefix_family
#print axioms accepted_generated_while_scalar_call_prefix_family
end Goose.Lower

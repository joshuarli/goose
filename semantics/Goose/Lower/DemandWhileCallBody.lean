import Goose.Lower.DemandCallLoopBody
import Goose.Lower.DemandWhileRecursiveBody

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_while_call_body_prefix {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state middle : St} (source : StmtSource cfg env (.while condition body origin) state)
    (branch : BlockSource cfg env [] body middle)
    (canonical : source.BlockChildAt branch 1 (by simp [DemandNode.child?, DemandNode.children]))
    {conditionFuel : Nat} (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool true) middle)
    {callContext : ContextId} {arguments : List Arg} {callOrigin statementOrigin : OriginId}
    (bodyStatements : body.stmts = [.expr (.call callContext arguments callOrigin) statementOrigin]) (noValue : body.value = none)
    {calleeContext : Context} {callee : Impl} (contextAt : cfg.mod.contexts[callContext]? = some calleeContext)
    (implAt : cfg.mod.impls[calleeContext.impl]? = some callee) (depth : env.depth < maxCallDepth)
    (fragment : ∀ current : St, WhileMixedStatements cfg
      { vars := callee.vars, act := current.nextAct, scopes := (callee.body.scope, current.nextScope) :: [], depth := env.depth + 1 } callee.body.stmts)
    {expression : Expr} (form : ControlPrefixExpression expression) (hasValue : callee.body.value = some expression)
    (shrink : cfg.mod.profile = .shrink)
    (argumentsForm : ∀ {innerState : St} (child : StmtSource cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } (.expr (.call callContext arguments callOrigin) statementOrigin) innerState),
      CallMixedArguments child.rootsEnv.access arguments)
    (stoppedArgumentsForm : ∀ {innerState : St} (child : StmtSource cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } (.expr (.call callContext arguments callOrigin) statementOrigin) innerState),
      CallMixedStoppedArguments child.rootsEnv.access arguments)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (targetConfig : cx.cfg = ⟨cfg.profile, lower cfg.mod⟩)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected branch.context)
    {headerState bodyStart bodyEnd jumped : LS} {header exitBlock bodyValue : Nat}
    {initial conditionFrame : GIR.Frame} {bodyPoint : Pt} {map required : RetainedSsaMap}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root branch.path
      (.block (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length,
        exitBlock, .jump header⟩) [] false body) bodyStart)
    (rows : GeneratedDemandRows cfg.mod branch.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile branch.context.retained)
    (headerBounded : map.Bounded headerState.vals.size) (bodyBounded : map.Bounded bodyStart.vals.size)
    (realized : map.Realizes cfg.mod branch.world env ⟨bodyPoint, conditionFrame, middle⟩)
    (headerInput : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv headerState initial (header, 0))
    (headerTarget : ∃ block, cx.fn.blocks[header]? = some block ∧ block.params = [])
    (bodyInput : GeneratedPrefixInput cfg env cx results
      (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
      branch.typingEnv branch.rootsEnv bodyStart conditionFrame bodyPoint)
    (bodyRun : lowerBlock (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length,
      exitBlock, .jump header⟩) [] false body (lowerEnv cfg.mod env.vars results) bodyStart = (bodyValue, bodyEnd))
    (bodyExtended : ExtT bodyEnd cx.fn.blocks)
    (jumpRun : emitTerm (.br header []) (lowerEnv cfg.mod env.vars results) bodyEnd = ((), jumped))
    (jumpExtended : ExtT jumped cx.fn.blocks)
    (entry : Evidence.RuntimePoint cx.cfg cx.fn bodyPoint conditionFrame middle)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨bodyPoint, conditionFrame, middle⟩ reached) :
    (GeneratedGenericBlockPrefixDemand branch selected map required bodyStart
      (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
      conditionFrame
      (@ReachableCallStatementFamilyCursor cfg { env with scopes := (body.scope, middle.nextScope) :: env.scopes } cx.fn results
        (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩))
      (GeneratedBranchBlockEffectDemand branch map required cx results bodyStart
        (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
        conditionFrame) reached) ∨
    ∃ (consumed remaining : Nat) (current : DemandRuntimePoint) (fuel : Nat) (next : StmtSource cfg env (.while condition body origin) current.state),
      consumed + remaining = taken ∧
      DemandRuntimePrefix cx consumed ⟨bodyPoint, conditionFrame, middle⟩ current ∧
      DemandRuntimePrefix cx remaining current reached ∧
      execBlock fuel cfg env [] body middle = .ok (.normal .unit) current.state ∧
      next.typingEnv = source.typingEnv ∧ next.rootsEnv = source.rootsEnv ∧ next.world = source.world ∧
      next.observation = source.observation ∧ next.plans = source.plans ∧ next.path = source.path ∧ HEq next.context source.context ∧
      GeneratedPrefixInput cfg env cx results none next.typingEnv next.rootsEnv headerState current.frame (header, 0) ∧
      map.Bounded headerState.vals.size ∧ map.Realizes cfg.mod next.world env ⟨(header, 0), current.frame, current.state⟩ ∧
      ∀ targetFuel, DemandInstructionStep cx targetFuel current ⟨(header, 0), current.frame, current.state⟩ := by
  cases cx with
  | mk current caller =>
    change current = ⟨cfg.profile, lower cfg.mod⟩ at targetConfig
    subst current
    have extended : ExtT (lowerBlock (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩) [] false body (lowerEnv cfg.mod env.vars results) bodyStart).2 caller.blocks := by
      rw [bodyRun]
      exact bodyExtended
    have agreement := accepted_generated_call_loop_body branch bodyStatements noValue contextAt implAt depth fragment form hasValue shrink
      argumentsForm stoppedArgumentsForm selected owned occurrence rows coverage admitted bodyBounded realized bodyInput extended entry
    have progress := agreement.1 steps
    cases progress.progress with
    | interior demanded => exact Or.inl demanded
    | @complete fuel consumed remaining current flow count executed residual done ended =>
      have normal := ended.normal
      subst flow
      obtain ⟨next, typing, roots, world, observation, plans, path, context, input, bounded, nextRealized, back⟩ :=
        accepted_generated_while_reentry source branch canonical conditionDone done headerInput headerTarget headerBounded
          bodyRun jumpRun jumpExtended ended
      exact Or.inr ⟨consumed, remaining, current, fuel, next, count, executed, residual, done,
        typing, roots, world, observation, plans, path, context, input, bounded, nextRealized, back⟩

theorem accepted_generated_while_call_body_stopped {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state middle : St} (source : StmtSource cfg env (.while condition body origin) state)
    (branch : BlockSource cfg env [] body middle)
    (canonical : source.BlockChildAt branch 1 (by simp [DemandNode.child?, DemandNode.children]))
    {conditionFuel : Nat} (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool true) middle)
    {callContext : ContextId} {arguments : List Arg} {callOrigin statementOrigin : OriginId}
    (bodyStatements : body.stmts = [.expr (.call callContext arguments callOrigin) statementOrigin]) (noValue : body.value = none)
    {calleeContext : Context} {callee : Impl} (contextAt : cfg.mod.contexts[callContext]? = some calleeContext)
    (implAt : cfg.mod.impls[calleeContext.impl]? = some callee) (depth : env.depth < maxCallDepth)
    (fragment : ∀ current : St, WhileMixedStatements cfg
      { vars := callee.vars, act := current.nextAct, scopes := (callee.body.scope, current.nextScope) :: [], depth := env.depth + 1 } callee.body.stmts)
    {expression : Expr} (form : ControlPrefixExpression expression) (hasValue : callee.body.value = some expression)
    (shrink : cfg.mod.profile = .shrink)
    (argumentsForm : ∀ {innerState : St} (child : StmtSource cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } (.expr (.call callContext arguments callOrigin) statementOrigin) innerState),
      CallMixedArguments child.rootsEnv.access arguments)
    (stoppedArgumentsForm : ∀ {innerState : St} (child : StmtSource cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } (.expr (.call callContext arguments callOrigin) statementOrigin) innerState),
      CallMixedStoppedArguments child.rootsEnv.access arguments)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (targetConfig : cx.cfg = ⟨cfg.profile, lower cfg.mod⟩)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected branch.context)
    {headerState bodyStart bodyEnd jumped : LS} {header exitBlock bodyValue : Nat}
    {initial conditionFrame : GIR.Frame} {bodyPoint : Pt} {map required : RetainedSsaMap}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root branch.path
      (.block (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length,
        exitBlock, .jump header⟩) [] false body) bodyStart)
    (rows : GeneratedDemandRows cfg.mod branch.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile branch.context.retained)
    (headerBounded : map.Bounded headerState.vals.size) (bodyBounded : map.Bounded bodyStart.vals.size)
    (realized : map.Realizes cfg.mod branch.world env ⟨bodyPoint, conditionFrame, middle⟩)
    (headerInput : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv headerState initial (header, 0))
    (headerTarget : ∃ block, cx.fn.blocks[header]? = some block ∧ block.params = [])
    (bodyInput : GeneratedPrefixInput cfg env cx results
      (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
      branch.typingEnv branch.rootsEnv bodyStart conditionFrame bodyPoint)
    (bodyRun : lowerBlock (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length,
      exitBlock, .jump header⟩) [] false body (lowerEnv cfg.mod env.vars results) bodyStart = (bodyValue, bodyEnd))
    (bodyExtended : ExtT bodyEnd cx.fn.blocks)
    (jumpRun : emitTerm (.br header []) (lowerEnv cfg.mod env.vars results) bodyEnd = ((), jumped))
    (jumpExtended : ExtT jumped cx.fn.blocks)
    (entry : Evidence.RuntimePoint cx.cfg cx.fn bodyPoint conditionFrame middle)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨bodyPoint, conditionFrame, middle⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    (∃ fuel, execBlock fuel cfg env [] body middle = .stop stop after) ∨
    ∃ (consumed remaining : Nat) (current : DemandRuntimePoint) (fuel : Nat) (next : StmtSource cfg env (.while condition body origin) current.state),
      consumed + remaining = taken ∧
      DemandRuntimePrefix cx consumed ⟨bodyPoint, conditionFrame, middle⟩ current ∧
      DemandRuntimePrefix cx remaining current reached ∧
      execBlock fuel cfg env [] body middle = .ok (.normal .unit) current.state ∧
      next.typingEnv = source.typingEnv ∧ next.rootsEnv = source.rootsEnv ∧ next.world = source.world ∧
      next.observation = source.observation ∧ next.plans = source.plans ∧ next.path = source.path ∧ HEq next.context source.context ∧
      GeneratedPrefixInput cfg env cx results none next.typingEnv next.rootsEnv headerState current.frame (header, 0) ∧
      map.Bounded headerState.vals.size ∧ map.Realizes cfg.mod next.world env ⟨(header, 0), current.frame, current.state⟩ ∧
      ∀ targetFuel, DemandInstructionStep cx targetFuel current ⟨(header, 0), current.frame, current.state⟩ := by
  cases cx with
  | mk current caller =>
    change current = ⟨cfg.profile, lower cfg.mod⟩ at targetConfig
    subst current
    have extended : ExtT (lowerBlock (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩) [] false body (lowerEnv cfg.mod env.vars results) bodyStart).2 caller.blocks := by
      rw [bodyRun]
      exact bodyExtended
    have agreement := accepted_generated_call_loop_body branch bodyStatements noValue contextAt implAt depth fragment form hasValue shrink
      argumentsForm stoppedArgumentsForm selected owned occurrence rows coverage admitted bodyBounded realized bodyInput extended entry
    have progress := agreement.2 steps stopped nonTimeout
    cases progress with
    | aborted fuel done => exact Or.inl ⟨fuel, done⟩
    | @complete fuel consumed remaining current flow count executed residual done ended =>
      have normal := ended.normal
      subst flow
      obtain ⟨next, typing, roots, world, observation, plans, path, context, input, bounded, nextRealized, back⟩ :=
        accepted_generated_while_reentry source branch canonical conditionDone done headerInput headerTarget headerBounded
          bodyRun jumpRun jumpExtended ended
      exact Or.inr ⟨consumed, remaining, current, fuel, next, count, executed, residual, done,
        typing, roots, world, observation, plans, path, context, input, bounded, nextRealized, back⟩


#print axioms accepted_generated_while_call_body_prefix
#print axioms accepted_generated_while_call_body_stopped
end Goose.Lower

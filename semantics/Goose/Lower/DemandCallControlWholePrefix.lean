import Goose.Lower.DemandCallWholePrefix
import Goose.Lower.DemandCallControlActualSuccess

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_control_call_prefix {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl) (depth : env.depth < maxCallDepth)
    (fragment : ∀ middle : St, WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    {expression : Expr} (form : ControlPrefixExpression expression) (hasValue : impl.body.value = some expression)
    {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod caller (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results loop
      source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    (shrink : cfg.mod.profile = .shrink) (argumentsForm : CallMixedArguments source.rootsEnv.access arguments)
    (callerStart : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached) :
    CallWholePrefix source caller results before loop map initial start taken reached := by
  have progress := accepted_generated_call_mixed_prefix_cells source selected owned occurrence rows coverage admitted bounded
    realized input extended shrink argumentsForm steps
  rcases progress.frontier extended with ⟨_, cursor, current, progress⟩ | ⟨argumentFuel, consumed, remaining, boundary, values,
      count, argumentSteps, residual, argumentsDone, current, callPost, read, instruction⟩
  · exact .arguments cursor current progress
  · have callerPoint : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller boundary.point boundary.frame boundary.state :=
      argumentSteps.reachable callerStart
    rcases residual.uncons with ⟨_, same⟩ | ⟨rest, next, length, first, later⟩
    · subst reached
      exact .ready argumentsDone current callPost read instruction
    · cases next
      cases first with
      | effect found execution => cases instruction.symm.trans found
      | branch found test enter => cases instruction.symm.trans found
      | branchTrue found test read enter => cases instruction.symm.trans found
      | branchFalse found test read enter => cases instruction.symm.trans found
      | define found execution =>
        cases instruction.symm.trans found
        obtain ⟨value, rfl⟩ := callOp_success_value execution
        obtain ⟨built, sourceFuel, evaluated, builtEq, step, boundaryResult⟩ :=
          accepted_generated_actual_control_call_success source argumentsDone contextAt implAt depth (fragment boundary.state)
            form hasValue callPost read callerPoint extended admitted bounded realized execution
        subst built
        exact .complete (by omega) (argumentSteps.append (.next step (.zero _))) later evaluated boundaryResult

#print axioms accepted_generated_control_call_prefix
end Goose.Lower

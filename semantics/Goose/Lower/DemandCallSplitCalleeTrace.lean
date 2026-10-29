import Goose.Lower.DemandCallSplitCalleeForward
import Goose.Lower.DemandCalleePrologueForward

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_split_call_callee_trace {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    {caller : Func} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod caller (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (form : SplitMixedArguments source.rootsEnv.access arguments) {initial : GIR.Frame} {start : Pt}
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results loop
      source.typingEnv source.rootsEnv before initial start)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (coverage : map.Covers required) (shrink : cfg.mod.profile = .shrink)
    {sourceFuel : Nat} {sourceValues : List Val} {sourceAfter : St}
    (sourceDone : mapList (evalArg sourceFuel cfg env) arguments state = .ok sourceValues sourceAfter)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    (callerStart : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state)
    (count : Nat) (bound : count ≤ sourceValues.length) :
    sourceAfter = state ∧ ∃ (length : Nat) (point : Pt) (frame : GIR.Frame)
      (body : BlockSource cfg ⟨impl.vars, state.nextAct, [], env.depth + 1⟩
        ((impl.params.toList.zip sourceValues).map fun item => (item.1.var, item.2)) impl.body
        { state with nextAct := state.nextAct + 1 }),
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ length ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (count + 1)
        ⟨(0, 0), callFrame impl state.nextAct (env.depth + 1) sourceValues, { state with nextAct := state.nextAct + 1 }⟩
        ⟨(0, 1 + count), { (callFrame impl state.nextAct (env.depth + 1) sourceValues) with scopes := [(impl.body.scope, state.nextScope)] },
          { state with nextAct := state.nextAct + 1, nextScope := state.nextScope + 1, store := preStore state.nextAct state.nextScope (((impl.params.toList.zip sourceValues).map fun item => (item.1.var, item.2)).take count) state.store }⟩ ∧
      Nonempty (ParameterPrefixCursor body count) ∧
      RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 1 + count)
        { (callFrame impl state.nextAct (env.depth + 1) sourceValues) with scopes := [(impl.body.scope, state.nextScope)] }
        { state with nextAct := state.nextAct + 1, nextScope := state.nextScope + 1, store := preStore state.nextAct state.nextScope (((impl.params.toList.zip sourceValues).map fun item => (item.1.var, item.2)).take count) state.store } ∧
      map.Realizes cfg.mod source.world env ⟨point, frame,
        { state with nextAct := state.nextAct + 1, nextScope := state.nextScope + 1, store := preStore state.nextAct state.nextScope (((impl.params.toList.zip sourceValues).map fun item => (item.1.var, item.2)).take count) state.store }⟩ := by
  have arity := source.call_arguments_arity contextAt implAt sourceDone
  obtain ⟨same, length, point, frame, body, callerSteps, cursor, atBody, retained⟩ :=
    accepted_generated_split_call_callee_forward source contextAt implAt depth occurrence rows form input admitted bounded realized
      coverage shrink sourceDone extended callerStart count bound
  have calleeSteps := accepted_callee_parameter_prologue_trace (ctx := ctx) body arity count bound
  exact ⟨same, length, point, frame, body, callerSteps, calleeSteps, cursor, atBody, retained⟩

#print axioms accepted_generated_split_call_callee_trace
end Goose.Lower

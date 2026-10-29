import Goose.Lower.DemandCallSplitMixedArgumentsForward
import Goose.Lower.DemandCallArguments

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_generated_split_call_callee_forward {cfg : Cfg} {env : Env} {state : St}
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
      Nonempty (ParameterPrefixCursor body count) ∧
      RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 1 + count)
        { (callFrame impl state.nextAct (env.depth + 1) sourceValues) with scopes := [(impl.body.scope, state.nextScope)] }
        { state with nextAct := state.nextAct + 1, nextScope := state.nextScope + 1, store := preStore state.nextAct state.nextScope (((impl.params.toList.zip sourceValues).map fun item => (item.1.var, item.2)).take count) state.store } ∧
      map.Realizes cfg.mod source.world env ⟨point, frame,
        { state with nextAct := state.nextAct + 1, nextScope := state.nextScope + 1, store := preStore state.nextAct state.nextScope (((impl.params.toList.zip sourceValues).map fun item => (item.1.var, item.2)).take count) state.store }⟩ := by
  obtain ⟨stateEq, length, point, frame, aliases, slots, steps, split, finalBounded, carried, checked, wholePost, cells, read, finalInput⟩ :=
    accepted_generated_call_split_mixed_arguments_forward source occurrence rows form input admitted bounded realized coverage shrink sourceDone extended
  subst sourceAfter
  let le := lowerEnv cfg.mod env.vars results
  obtain ⟨ids, middle, afterCall, argsRun, definition, tail⟩ := lowerExpr_call_split
    (show lowerExpr (.call context arguments origin) le before =
      ((lowerExpr (.call context arguments origin) le before).1, (lowerExpr (.call context arguments origin) le before).2) from rfl)
  have afterExtended : ExtT afterCall caller.blocks := by
    rcases tail with ⟨_, term⟩ | ⟨_, rfl⟩
    · exact extended.of_adv (adv_emitTerm term)
    · exact extended
  have sameIds : ids = (lowerArgs arguments le before).1 := by rw [argsRun]
  have sameMiddle : middle = (lowerArgs arguments le before).2 := by rw [argsRun]
  subst ids
  subst middle
  have instruction := (emitDef_facts definition finalInput.atPoint afterExtended).2.2.2.2
  have depthEq : frame.depth = env.depth := finalInput.related.depth
  have targetDepth : frame.depth < maxCallDepth := by simpa [depthEq] using depth
  have mapCarried : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩ := by
    constructor
    · intro cell member
      exact carried.1.1 cell (List.mem_append_right _ member)
    · exact carried.1.2
  obtain ⟨body, prefixProof, atBody, preserved⟩ := accepted_actual_call_arguments_entry source sourceDone contextAt implAt
    (steps.reachable callerStart) instruction depthEq targetDepth read mapCarried count bound
  exact ⟨rfl, length, point, frame, body, steps, prefixProof, atBody, preserved⟩

#print axioms accepted_generated_split_call_callee_forward
end Goose.Lower

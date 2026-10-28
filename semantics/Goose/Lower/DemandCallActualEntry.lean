import Goose.Lower.DemandCallMixedStoppedCells
import Goose.Lower.DemandCallArguments

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem CallMixedStoppedCells.actualCalleeEntry {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    {source : ExprSource cfg env (.call context arguments origin) state}
    {cx : FnCtx} {results : List Ty} {before : LS} {loop : Option LoopCtx} {map : RetainedSsaMap}
    {initial : GIR.Frame} {start : Pt} {taken : Nat} {reached : DemandRuntimePoint} {stop : Stop} {after : St}
    (outcome : CallMixedStoppedCells source cx results before loop map [] 0 arguments ⟨start, initial, state⟩ taken reached stop after)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (callerStart : RuntimePoint cx.cfg cx.fn start initial state) (depth : env.depth < maxCallDepth) :
    (∃ fuel, mapList (evalArg fuel cfg env) arguments state = .stop stop after) ∨
    ∃ (boundary : DemandRuntimePoint) (values : List Val) (ctx : Context) (impl : Impl),
      cfg.mod.contexts[context]? = some ctx ∧ cfg.mod.impls[ctx.impl]? = some impl ∧
      ∃ body : BlockSource cfg ⟨impl.vars, boundary.state.nextAct, [], env.depth + 1⟩
        ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
        { boundary.state with nextAct := boundary.state.nextAct + 1 },
        Nonempty (ParameterPrefixCursor body 0) ∧
        RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 1)
          { (callFrame impl boundary.state.nextAct (env.depth + 1) values) with scopes := [(impl.body.scope, boundary.state.nextScope)] }
          { boundary.state with nextAct := boundary.state.nextAct + 1, nextScope := boundary.state.nextScope + 1, store := preStore boundary.state.nextAct boundary.state.nextScope [] boundary.state.store } ∧
        ∃ prior : List (ValueId × RetainedAlias),
          (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env
            ⟨boundary.point, boundary.frame,
              { boundary.state with nextAct := boundary.state.nextAct + 1, nextScope := boundary.state.nextScope + 1, store := preStore boundary.state.nextAct boundary.state.nextScope [] boundary.state.store }⟩ := by
  cases outcome with
  | aborted trace => exact Or.inl trace.fuel.2
  | @complete consumed remaining boundary values prior count executed residual trace tracked bounded realized cells input =>
    obtain ⟨sourceFuel, evaluated⟩ := trace.fuel
    have read := cells.read boundary.state
    let le := lowerEnv cfg.mod env.vars results
    obtain ⟨ids, middle, afterCall, argsRun, definition, tail⟩ := lowerExpr_call_split
      (show lowerExpr (.call context arguments origin) le before =
        ((lowerExpr (.call context arguments origin) le before).1, (lowerExpr (.call context arguments origin) le before).2) from rfl)
    have afterExtended : ExtT afterCall cx.fn.blocks := by
      rcases tail with ⟨_, term⟩ | ⟨_, rfl⟩
      · exact extended.of_adv (adv_emitTerm term)
      · exact extended
    have sameIds : ids = (lowerArgs arguments le before).1 := by rw [argsRun]
    have sameMiddle : middle = (lowerArgs arguments le before).2 := by rw [argsRun]
    subst ids
    subst middle
    have point : (lowerArgs arguments le before).2.pp = some boundary.point := by simpa using input.atPoint
    have instruction := (emitDef_facts definition point afterExtended).2.2.2.2
    have callerPoint := executed.reachable callerStart
    have cfgEq : cx.cfg = ⟨cfg.profile, lower cfg.mod⟩ := by
      cases configEq : cx.cfg with
      | mk profile mod =>
        have profileEq := input.related.prof
        have moduleEq := input.moduleEq
        rw [configEq] at profileEq moduleEq
        simp only at profileEq moduleEq
        cases profileEq
        cases moduleEq
        rfl
    rw [cfgEq] at callerPoint
    obtain ⟨ctx, impl, contextAt, implAt, body, typing, roots, path, owner⟩ :=
      source.calleeAfterArgs sourceFuel values evaluated
    have depthAt : boundary.frame.depth = env.depth := input.related.depth
    have targetDepth : boundary.frame.depth < maxCallDepth := by simpa [depthAt] using depth
    have entry := accepted_actual_call_arguments_entry source evaluated contextAt implAt callerPoint instruction
      depthAt targetDepth (by simpa using read) realized 0 (by omega)
    obtain ⟨newBody, prefixProof, atBody, preserved⟩ := entry
    exact Or.inr ⟨boundary, values, ctx, impl, contextAt, implAt, newBody, prefixProof, by simpa using atBody, prior, by simpa using preserved⟩

#print axioms CallMixedStoppedCells.actualCalleeEntry
end Goose.Lower

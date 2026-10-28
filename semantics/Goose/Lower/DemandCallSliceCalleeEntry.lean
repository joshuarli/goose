import Goose.Lower.DemandCallSliceSequence
import Goose.Lower.DemandCallArguments

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_call_slice_callee_entry {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {caller : Func} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod caller (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (form : LocalSliceArguments source.rootsEnv.access arguments) {initial : GIR.Frame} {start : Pt}
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results loop
      source.typingEnv source.rootsEnv before initial start)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    (callerStart : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state)
    (depth : env.depth < maxCallDepth) :
    ∃ (fuel length : Nat) (point : Pt) (frame : GIR.Frame) (values : List Val) (slots : List SliceSlotArgumentCell)
      (ctx : Context) (impl : Impl),
      mapList (evalArg fuel cfg env) arguments state = .ok values state ∧
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ length ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      cfg.mod.contexts[context]? = some ctx ∧ cfg.mod.impls[ctx.impl]? = some impl ∧
      ∃ body : BlockSource cfg ⟨impl.vars, state.nextAct, [], env.depth + 1⟩
        ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
        { state with nextAct := state.nextAct + 1 },
      Nonempty (ParameterPrefixCursor body 0) ∧
      RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 1)
        { (callFrame impl state.nextAct (env.depth + 1) values) with scopes := [(impl.body.scope, state.nextScope)] }
        { state with nextAct := state.nextAct + 1, nextScope := state.nextScope + 1, store := preStore state.nextAct state.nextScope [] state.store } ∧
      (⟨map, slots⟩ : SplitCallRetained).Realizes cfg.mod source.world env
        ⟨point, frame, { state with nextAct := state.nextAct + 1, nextScope := state.nextScope + 1, store := preStore state.nextAct state.nextScope [] state.store }⟩ := by
  obtain ⟨fuel, length, point, frame, values, slots, evaluated, executed, split, bound, carried, checked, cells, read, finalInput⟩ :=
    accepted_generated_call_slice_arguments source occurrence rows form input bounded realized extended
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
  have callerPoint := executed.reachable callerStart
  obtain ⟨ctx, impl, contextAt, implAt, body, typing, roots, path, owner⟩ :=
    source.calleeAfterArgs fuel values evaluated
  have depthAt : frame.depth = env.depth := finalInput.related.depth
  have targetDepth : frame.depth < maxCallDepth := by simpa [depthAt] using depth
  obtain ⟨newBody, prefixProof, atBody, ordinary⟩ :=
    accepted_actual_call_arguments_entry source evaluated contextAt implAt callerPoint instruction
      depthAt targetDepth (by simpa using read) carried.1 0 (by omega)
  refine ⟨fuel, length, point, frame, values, slots, ctx, impl, evaluated, executed, contextAt, implAt,
    newBody, prefixProof, by simpa using atBody, ordinary, ?_⟩
  simpa [SliceSlotArgumentCells.Realizes, preStore] using carried.2

#print axioms accepted_generated_call_slice_callee_entry
end Goose.Lower

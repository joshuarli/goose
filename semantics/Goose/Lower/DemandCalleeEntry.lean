import Goose.Lower.DemandParameterPrologue

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence
open Goose.Proofs.Lower (extT_finish bodyTail)

theorem lowered_function_entry_canonical {cfg : Cfg} {ctx : Context} {impl : Impl} {depth : Nat}
    {values : List Val} {before after : St} {frame : GIR.Frame}
    (entry : FunctionEntry (lowerContextAt cfg.mod ctx impl) depth values before frame after) :
    impl.params.size = values.length ∧
      frame = callFrame impl before.nextAct depth values ∧ after = { before with nextAct := before.nextAct + 1 } := by
  have arity : impl.params.size = values.length := by
    simpa [lowerContextAt, lowerImpl] using entry.1
  obtain ⟨act, fresh, actEq, freshEq, entered⟩ := entry.activation
  subst act
  subst fresh
  let le := lowerEnv cfg.mod impl.vars impl.results.toList
  let body := lowerBlock none (callPre impl) false impl.body le (callEntry impl)
  have tailExtension : ExtT (bodyTail impl le body.1 body.2) (lowerContextAt cfg.mod ctx impl).blocks := by
    rw [lowerContextAt_blocks, lowerImpl_call_blocks]
    exact extT_finish _
  have bodyExtension := tailExtension.of_adv
    (advB_finishFunction impl body.1 le body.2 (finishFunction impl body.1 le body.2).1
      (bodyTail impl le body.1 body.2) rfl)
  have entryExtension : ExtT (callEntry impl) (lowerContextAt cfg.mod ctx impl).blocks :=
    bodyExtension.of_adv (advB_lowerBlock none (callPre impl) false impl.body _ _ _ _ rfl)
  obtain ⟨block, blockAt, params⟩ := entryExtension.params (b := 0)
    (blk := ⟨(List.range impl.params.size).zip (callEntryTypes impl), #[]⟩) rfl
  have length : ((List.range impl.params.size).zip (callEntryTypes impl)).length = values.length := by
    simp [callEntryTypes, arity]
  simp only [enterBlock, blockAt, params, List.length_map, length, ite_true, bindParams_call, bind_apply, pure_apply,
    Res.ok.injEq, Prod.mk.injEq] at entered
  exact ⟨arity, entered.1.2.symm, entered.2.symm⟩

theorem accepted_actual_callee_parameter_prefix {cfg : Cfg} {env : Env} {state after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {sourceFuel : Nat} {values : List Val}
    (argumentsDone : mapList (evalArg sourceFuel cfg env) arguments state = .ok values after)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    {caller : Func} {point : Pt} {callerFrame : GIR.Frame} {result : ValueId} {ids : List ValueId}
    (callerPoint : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point callerFrame after)
    (instruction : instAt caller point = some (.def result (.call context ids (some origin))))
    (depthEq : callerFrame.depth = env.depth) (depth : callerFrame.depth < maxCallDepth)
    (read : mapList (getVal callerFrame) ids after = .ok values after)
    {calleeFrame : GIR.Frame} {entered : St}
    (entry : FunctionEntry (lowerContextAt cfg.mod ctx impl) (callerFrame.depth + 1) values after calleeFrame entered)
    {map : RetainedSsaMap} {world : World}
    (retained : map.Realizes cfg.mod world env ⟨point, callerFrame, after⟩)
    (count : Nat) (bound : count ≤ values.length) :
    ∃ body : BlockSource cfg ⟨impl.vars, after.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)) impl.body
      { after with nextAct := after.nextAct + 1 },
      Nonempty (ParameterPrefixCursor body count) ∧
      RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 1 + count)
        { (callFrame impl after.nextAct (env.depth + 1) values) with scopes := [(impl.body.scope, after.nextScope)] }
        { after with nextAct := after.nextAct + 1, nextScope := after.nextScope + 1, store := preStore after.nextAct after.nextScope (((impl.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)).take count) after.store } ∧
      map.Realizes cfg.mod world env ⟨point, callerFrame,
        { after with nextAct := after.nextAct + 1, nextScope := after.nextScope + 1, store := preStore after.nextAct after.nextScope (((impl.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)).take count) after.store }⟩ := by
  obtain ⟨actualCtx, actualImpl, actualContext, actualImplAt, body, typing, roots, path, owner⟩ :=
    source.calleeAfterArgs sourceFuel values argumentsDone
  have ctxEq : actualCtx = ctx := Option.some.inj (actualContext.symm.trans contextAt)
  subst actualCtx
  have implEq : actualImpl = impl := Option.some.inj (actualImplAt.symm.trans implAt)
  subst actualImpl
  obtain ⟨arity, frameEq, stateEq⟩ := lowered_function_entry_canonical entry
  have reached : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl)
      (0, 0) calleeFrame entered := by
    exact RuntimePoint.call callerPoint instruction depth read (lower_func_at contextAt implAt) entry
  rw [frameEq, stateEq, depthEq] at reached
  have prologue := accepted_callee_parameter_prologue (ctx := ctx) body arity reached count bound
  refine ⟨body, prologue.1, ?_, ?_⟩
  · simpa using prologue.2.1
  · have carried : map.Realizes cfg.mod world env
        ⟨point, callerFrame, { after with nextAct := after.nextAct + 1 }⟩ := by
      simpa only [RetainedSsaMap.Realizes, RetainedOperandsAt] using retained
    simpa using prologue.2.2 map world env point callerFrame carried

#print axioms lowered_function_entry_canonical
#print axioms accepted_actual_callee_parameter_prefix
end Goose.Lower

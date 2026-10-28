import Goose.Lower.DemandCallActualCalleeRun

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem actual_call_success_callee_run {cfg : GCfg} {caller callee : Func} {context : ContextId}
    {ids : List ValueId} {values : List Val} {frame : GIR.Frame} {state after : St} {origin : Option OriginId}
    (below : frame.depth < maxCallDepth)
    (read : mapList (getVal frame) ids state = .ok values state)
    (lookup : cfg.mod.funcs[context]? = some callee)
    {calleeFrame : GIR.Frame} {entered : St}
    (entry : FunctionEntry callee (frame.depth + 1) values state calleeFrame entered)
    {fuel : Nat} {value : Val}
    (executed : execOp fuel ⟨cfg, caller⟩ frame (.call context ids origin) state = .ok (.val value) after) :
    ∃ calleeFuel, runAt ⟨cfg, callee⟩ (0, 0) calleeFrame calleeFuel entered = .ok value after := by
  cases fuel with
  | zero => simp [execOp, timeout, M.stop] at executed
  | succ fuel =>
    simp only [execOp, bind_apply, read] at executed
    cases fuel with
    | zero => simp [callFn, timeout, M.stop] at executed
    | succ fuel =>
      simp only [callFn, Nat.not_le_of_lt below, ↓reduceIte, lookupFn, lookup, pure_apply, bind_apply] at executed
      cases fuel with
      | zero => simp [enterFn, timeout, M.stop] at executed
      | succ fuel =>
        rw [entry.enterFn fuel] at executed
        cases run : exec fuel ⟨cfg, callee⟩ calleeFrame (instsAt callee (0, 0)) entered with
        | stop reason final => rw [run] at executed; cases executed
        | ok result final =>
          rw [run] at executed
          simp only [Res.ok.injEq, RVal.val.injEq] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact ⟨fuel, by simpa only [runAt] using run⟩


theorem actual_call_stopped_callee_run {cfg : GCfg} {caller callee : Func} {context : ContextId}
    {ids : List ValueId} {values : List Val} {frame : GIR.Frame} {state after : St} {origin : Option OriginId}
    (below : frame.depth < maxCallDepth)
    (read : mapList (getVal frame) ids state = .ok values state)
    (lookup : cfg.mod.funcs[context]? = some callee)
    {calleeFrame : GIR.Frame} {entered : St}
    (entry : FunctionEntry callee (frame.depth + 1) values state calleeFrame entered)
    {fuel : Nat} {stop : Stop}
    (nonTimeout : stop ≠ .timeout)
    (executed : execOp fuel ⟨cfg, caller⟩ frame (.call context ids origin) state = .stop stop after) :
    ∃ calleeFuel, runAt ⟨cfg, callee⟩ (0, 0) calleeFrame calleeFuel entered = .stop stop after := by
  cases fuel with
  | zero => simp [execOp, timeout, M.stop] at executed; exact (nonTimeout executed.1.symm).elim
  | succ fuel =>
    simp only [execOp, bind_apply, read] at executed
    cases fuel with
    | zero => simp [callFn, timeout, M.stop] at executed; exact (nonTimeout executed.1.symm).elim
    | succ fuel =>
      simp only [callFn, Nat.not_le_of_lt below, ↓reduceIte, lookupFn, lookup, pure_apply, bind_apply] at executed
      cases fuel with
      | zero => simp [enterFn, timeout, M.stop] at executed; exact (nonTimeout executed.1.symm).elim
      | succ fuel =>
        rw [entry.enterFn fuel] at executed
        cases run : exec fuel ⟨cfg, callee⟩ calleeFrame (instsAt callee (0, 0)) entered with
        | stop reason final =>
          rw [run] at executed
          simp only [Res.stop.injEq] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact ⟨fuel, by simpa only [runAt] using run⟩
        | ok result final => rw [run] at executed; cases executed

theorem accepted_generated_call_execution_frontier {cfg : Cfg} {env : Env} {state middle after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val}
    (argumentsDone : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    {caller : Func} {before : LS} {results : List Ty} {initial frame : GIR.Frame} {point : Pt}
    (wholePost : Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial
      (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2 frame point [])
    (read : mapList (getVal frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 middle = .ok values middle)
    (callerPoint : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    {targetFuel : Nat} {value : Val}
    (executed : execOp targetFuel ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ frame
      (.call context (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 (some origin)) middle = .ok (.val value) after) :
    ∃ afterCall : LS, ∃ calleeFuel,
      afterCall = (emitDef (.call context (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 (some origin))
        (lowerEnv cfg.mod env.vars results) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2).2 ∧
      RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 0)
        (callFrame impl middle.nextAct (env.depth + 1) values) { middle with nextAct := middle.nextAct + 1 } ∧
      runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (0, 0)
        (callFrame impl middle.nextAct (env.depth + 1) values) calleeFuel { middle with nextAct := middle.nextAct + 1 } = .ok value after ∧
      Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial afterCall
        (frame.set (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.val value))
        (point.1, point.2 + 1) [((lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1, .val value)] ∧
      RuntimeStep ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle (point.1, point.2 + 1)
        (frame.set (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.val value)) after := by
  let le := lowerEnv cfg.mod env.vars results
  obtain ⟨ids, middleBuilder, afterCall, argsRun, definition, tail⟩ := lowerExpr_call_split
    (show lowerExpr (.call context arguments origin) le before =
      ((lowerExpr (.call context arguments origin) le before).1, (lowerExpr (.call context arguments origin) le before).2) from rfl)
  have afterExtended : ExtT afterCall caller.blocks := by
    rcases tail with ⟨_, term⟩ | ⟨_, rfl⟩
    · exact extended.of_adv (adv_emitTerm term)
    · exact extended
  have idsEq : ids = (lowerArgs arguments le before).1 := by rw [argsRun]
  have middleEq : middleBuilder = (lowerArgs arguments le before).2 := by rw [argsRun]
  subst ids
  subst middleBuilder
  obtain ⟨post, instruction⟩ := Post.def_leaf wholePost definition afterExtended (.val value)
  have arity := source.call_arguments_arity contextAt implAt argumentsDone
  have depthAt : frame.depth = env.depth := wholePost.rel.depth
  have below : frame.depth < maxCallDepth := by simpa [depthAt] using depth
  have entry := lowered_function_entry_generated (cfg := cfg) (ctx := ctx) (impl := impl)
    (depth := env.depth + 1) (values := values) (state := middle) arity
  have callerEntry : FunctionEntry (lowerContextAt cfg.mod ctx impl) (frame.depth + 1) values middle
      (callFrame impl middle.nextAct (env.depth + 1) values) { middle with nextAct := middle.nextAct + 1 } := by
    simpa [depthAt] using entry
  have lookup := lower_func_at contextAt implAt
  have calleePoint : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 0)
      (callFrame impl middle.nextAct (env.depth + 1) values) { middle with nextAct := middle.nextAct + 1 } :=
    .call callerPoint instruction below read lookup callerEntry
  obtain ⟨calleeFuel, calleeRun⟩ := actual_call_success_callee_run below read lookup callerEntry executed
  exact ⟨afterCall, calleeFuel, (by rw [definition]), calleePoint, calleeRun, post, .define instruction executed⟩

#print axioms accepted_generated_call_execution_frontier
#print axioms actual_call_stopped_callee_run
#print axioms actual_call_success_callee_run
end Goose.Lower

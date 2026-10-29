import Goose.Lower.DemandCallSliceActualRun
import Goose.Lower.DemandCallActualInstructionStop

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_actual_slice_unit_call_instruction_stop {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val}
    (argumentsDone : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    (fragment : SliceAssignmentStatements impl.body.stmts)
    (noResults : impl.results.toList = []) (noValue : impl.body.value = none)
    {caller : Func} {before : LS} {results : List Ty} {initial frame : GIR.Frame} {point : Pt}
    (wholePost : Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial
      (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2 frame point [])
    (read : mapList (getVal frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 middle = .ok values middle)
    (callerPoint : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (executed : execOp targetFuel ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ frame
      (.call context (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 (some origin)) middle = .stop stop after)
    (nonTimeout : stop ≠ .timeout) :
    ∃ sourceFuel, evalExpr sourceFuel cfg env (.call context arguments origin) state = .stop stop after := by
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
  obtain ⟨_, instruction⟩ := Post.def_leaf wholePost definition afterExtended (.val .unit)
  have arity := source.call_arguments_arity contextAt implAt argumentsDone
  have depthAt : frame.depth = env.depth := wholePost.rel.depth
  have below : frame.depth < maxCallDepth := by simpa [depthAt] using depth
  have entry := lowered_function_entry_generated (cfg := cfg) (ctx := ctx) (impl := impl)
    (depth := env.depth + 1) (values := values) (state := middle) arity
  have callerEntry : FunctionEntry (lowerContextAt cfg.mod ctx impl) (frame.depth + 1) values middle
      (callFrame impl middle.nextAct (env.depth + 1) values) { middle with nextAct := middle.nextAct + 1 } := by
    simpa [depthAt] using entry
  have calleePoint : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 0)
      (callFrame impl middle.nextAct (env.depth + 1) values) { middle with nextAct := middle.nextAct + 1 } :=
    .call callerPoint instruction below read (lower_func_at contextAt implAt) callerEntry
  obtain ⟨calleeFuel, calleeRun⟩ := actual_call_stopped_callee_run below read
    (lower_func_at contextAt implAt) callerEntry nonTimeout executed
  obtain ⟨bodyFuel, bodyStopped⟩ :=
    accepted_generated_slice_callee_unit_stopped_run source argumentsDone contextAt implAt fragment noResults noValue calleePoint calleeRun nonTimeout
  exact ⟨max argumentFuel bodyFuel + 2,
    accepted_call_source_stop source argumentsDone contextAt implAt depth nonTimeout bodyStopped⟩


#print axioms accepted_generated_actual_slice_unit_call_instruction_stop
end Goose.Lower

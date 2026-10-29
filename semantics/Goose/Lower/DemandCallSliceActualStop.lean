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
  apply accepted_generated_actual_unit_call_stop_of_callee source argumentsDone contextAt implAt depth ?_
    wholePost read callerPoint extended executed nonTimeout
  intro calleeFuel stop after entry run nonTimeout
  exact accepted_generated_slice_callee_unit_stopped_run source argumentsDone contextAt implAt fragment noResults noValue entry run nonTimeout

#print axioms accepted_generated_actual_slice_unit_call_instruction_stop
end Goose.Lower

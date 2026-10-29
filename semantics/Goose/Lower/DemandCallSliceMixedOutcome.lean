import Goose.Lower.DemandCallSliceMixedRun
import Goose.Lower.DemandCallSliceMutationOutcome

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_actual_slice_mixed_unit_call_success {cfg : Cfg} {env : Env} {state middle after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val}
    (argumentsDone : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    (fragment : SliceMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    (noResults : impl.results.toList = []) (noValue : impl.body.value = none)
    {caller : Func} {before : LS} {results : List Ty} {initial frame : GIR.Frame} {start point : Pt}
    (wholePost : Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial
      (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2 frame point [])
    (read : mapList (getVal frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 middle = .ok values middle)
    (callerPoint : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {targetFuel : Nat} {value : Val}
    (executed : execOp targetFuel ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ frame
      (.call context (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 (some origin)) middle = .ok (.val value) after) :
    value = .unit ∧ ∃ (afterCall : LS) (sourceFuel : Nat),
      evalExpr sourceFuel cfg env (.call context arguments origin) state = .ok value after ∧
      afterCall = (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 ∧
      RuntimeStep ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle (point.1, point.2 + 1)
        (frame.set (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.val value)) after ∧
      ExpressionDemandBoundary source map ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial afterCall
        (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 value after
        (point.1, point.2 + 1)
        (frame.set (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.val value)) := by
  apply accepted_generated_actual_unit_call_success_of_callee source argumentsDone contextAt implAt depth ?_
    wholePost read callerPoint extended admitted bounded realized executed
  intro calleeFuel value after entry run
  exact accepted_generated_slice_mixed_callee_unit_success source argumentsDone contextAt implAt fragment noResults noValue entry run


#print axioms accepted_generated_actual_slice_mixed_unit_call_success

theorem accepted_generated_actual_slice_mixed_unit_call_instruction_stop {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val}
    (argumentsDone : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    (fragment : SliceMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
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
  exact accepted_generated_slice_mixed_callee_unit_stopped_run source argumentsDone contextAt implAt fragment noResults noValue entry run nonTimeout


#print axioms accepted_generated_actual_slice_mixed_unit_call_instruction_stop

theorem accepted_generated_slice_mixed_call_outcomes {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    (fragment : SliceMixedStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := (impl.body.scope, state.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    (noResults : impl.results.toList = []) (noValue : impl.body.value = none)
    {caller : Func} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod caller (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (form : LocalSliceArguments source.rootsEnv.access arguments) {initial : GIR.Frame} {start : Pt}
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results loop
      source.typingEnv source.rootsEnv before initial start)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    (callerStart : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state) :
    ∃ (fuel length : Nat) (point : Pt) (frame : GIR.Frame) (values : List Val),
      mapList (evalArg fuel cfg env) arguments state = .ok values state ∧
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ length ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      instAt caller point = some (.def (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1
        (.call context (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 (some origin))) ∧
      (∀ targetFuel value after,
        execOp targetFuel ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ frame
          (.call context (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 (some origin)) state = .ok (.val value) after →
        value = .unit ∧ ∃ sourceFuel, evalExpr sourceFuel cfg env (.call context arguments origin) state = .ok value after) ∧
      (∀ targetFuel stop after,
        execOp targetFuel ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ frame
          (.call context (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 (some origin)) state = .stop stop after →
        stop ≠ .timeout → ∃ sourceFuel, evalExpr sourceFuel cfg env (.call context arguments origin) state = .stop stop after) := by
  obtain ⟨fuel, length, point, frame, values, evaluated, executed, wholePost, read, callerPoint, instruction⟩ :=
    accepted_generated_call_slice_frontier source occurrence rows form input bounded realized extended callerStart
  refine ⟨fuel, length, point, frame, values, evaluated, executed, instruction, ?_, ?_⟩
  · intro targetFuel value after actual
    obtain ⟨same, _, sourceFuel, sourceDone, _, _, _⟩ :=
      accepted_generated_actual_slice_mixed_unit_call_success source evaluated contextAt implAt depth fragment noResults noValue
        wholePost read callerPoint extended admitted bounded realized actual
    exact ⟨same, sourceFuel, sourceDone⟩
  · intro targetFuel stop after actual nonTimeout
    exact accepted_generated_actual_slice_mixed_unit_call_instruction_stop source evaluated contextAt implAt depth fragment noResults noValue
      wholePost read callerPoint extended actual nonTimeout


#print axioms accepted_generated_slice_mixed_call_outcomes
end Goose.Lower

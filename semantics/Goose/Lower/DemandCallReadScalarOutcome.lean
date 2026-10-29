import Goose.Lower.DemandCallReadScalarFrontier
import Goose.Lower.DemandCallSplitBooleanOutcome

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_read_scalar_mixed_call_outcomes {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {place : Place} {rest : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context (.byVal (.read place) :: rest) origin) state)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    (fragment : SliceMixedStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := (impl.body.scope, state.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    (noResults : impl.results.toList = []) (noValue : impl.body.value = none)
    {caller : Func} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod caller (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context (.byVal (.read place) :: rest) origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (readForm : ScalarReadPlace place) (form : LocalSliceScalarArguments source.rootsEnv.access rest) {initial : GIR.Frame} {start : Pt}
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results loop
      source.typingEnv source.rootsEnv before initial start)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (coverage : map.Covers required) (shrink : cfg.mod.profile = .shrink)
    (extended : ExtT (lowerExpr (.call context (.byVal (.read place) :: rest) origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    {taken : Nat} {runtime : DemandRuntimePoint} (completed : 2 ≤ taken)
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ runtime)
    (callerStart : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state) :
    ∃ (fuel length : Nat) (point : Pt) (frame : GIR.Frame) (values : List Val),
      mapList (evalArg fuel cfg env) (.byVal (.read place) :: rest) state = .ok values state ∧
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ length ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      instAt caller point = some (.def (lowerExpr (.call context (.byVal (.read place) :: rest) origin) (lowerEnv cfg.mod env.vars results) before).1
        (.call context (lowerArgs (.byVal (.read place) :: rest) (lowerEnv cfg.mod env.vars results) before).1 (some origin))) ∧
      (∀ targetFuel value after,
        execOp targetFuel ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ frame
          (.call context (lowerArgs (.byVal (.read place) :: rest) (lowerEnv cfg.mod env.vars results) before).1 (some origin)) state = .ok (.val value) after →
        value = .unit ∧ ∃ sourceFuel, evalExpr sourceFuel cfg env (.call context (.byVal (.read place) :: rest) origin) state = .ok value after) ∧
      (∀ targetFuel stop after,
        execOp targetFuel ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ frame
          (.call context (lowerArgs (.byVal (.read place) :: rest) (lowerEnv cfg.mod env.vars results) before).1 (some origin)) state = .stop stop after →
        stop ≠ .timeout → ∃ sourceFuel, evalExpr sourceFuel cfg env (.call context (.byVal (.read place) :: rest) origin) state = .stop stop after) := by
  obtain ⟨fuel, length, point, frame, values, evaluated, executed, wholePost, read, callerPoint, instruction⟩ :=
    accepted_generated_call_read_scalar_frontier source occurrence rows readForm form input admitted bounded realized coverage shrink extended completed steps callerStart
  refine ⟨fuel, length, point, frame, values, evaluated, executed, instruction, ?_, ?_⟩
  · intro targetFuel value after actual
    obtain ⟨same, _, sourceFuel, sourceDone, _, _, _⟩ :=
      accepted_generated_actual_slice_mixed_unit_call_success source evaluated contextAt implAt depth fragment noResults noValue
        wholePost read callerPoint extended admitted bounded realized actual
    exact ⟨same, sourceFuel, sourceDone⟩
  · intro targetFuel stop after actual nonTimeout
    exact accepted_generated_actual_slice_mixed_unit_call_instruction_stop source evaluated contextAt implAt depth fragment noResults noValue
      wholePost read callerPoint extended actual nonTimeout


#print axioms accepted_generated_read_scalar_mixed_call_outcomes
end Goose.Lower

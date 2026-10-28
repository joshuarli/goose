import Goose.Lower.DemandCallSliceSequence
import Goose.Lower.DemandCallActualInstructionStop
import Goose.Lower.DemandCallActualSuccess

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_slice_unit_call_outcomes {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    (fragment : WhileMixedStatements cfg
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
  obtain ⟨fuel, length, point, frame, values, slots, evaluated, executed, split, bound, carried, checked, wholePost, cells, read, finalInput⟩ :=
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
  refine ⟨fuel, length, point, frame, values, evaluated, executed, instruction, ?_, ?_⟩
  · intro targetFuel value after actual
    obtain ⟨same, _, sourceFuel, sourceDone, _, _, _⟩ :=
      accepted_generated_actual_unit_call_success source evaluated contextAt implAt depth fragment noResults noValue
        wholePost read callerPoint extended admitted bounded realized actual
    exact ⟨same, sourceFuel, sourceDone⟩
  · intro targetFuel stop after actual nonTimeout
    exact accepted_generated_actual_unit_call_instruction_stop source evaluated contextAt implAt depth fragment noResults noValue
      wholePost read callerPoint extended actual nonTimeout

#print axioms accepted_generated_slice_unit_call_outcomes
end Goose.Lower

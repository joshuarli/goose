import Goose.Lower.DemandCallReadScalarArguments
import Goose.Lower.DemandCallSplitBooleanFrontier

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_call_read_scalar_frontier {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {place : Place} {rest : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context (.byVal (.read place) :: rest) origin) state)
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
      Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial
        (lowerArgs (.byVal (.read place) :: rest) (lowerEnv cfg.mod env.vars results) before).2 frame point [] ∧
      mapList (getVal frame) (lowerArgs (.byVal (.read place) :: rest) (lowerEnv cfg.mod env.vars results) before).1 state = .ok values state ∧
      RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point frame state ∧
      instAt caller point = some (.def (lowerExpr (.call context (.byVal (.read place) :: rest) origin) (lowerEnv cfg.mod env.vars results) before).1
        (.call context (lowerArgs (.byVal (.read place) :: rest) (lowerEnv cfg.mod env.vars results) before).1 (some origin))) := by
  obtain ⟨fuel, length, point, frame, values, aliases, slots, evaluated, executed, split, bound, carried, checked, wholePost, cells, read, finalInput⟩ :=
    accepted_generated_call_read_scalar_arguments source occurrence rows readForm form input admitted bounded realized coverage shrink extended completed steps
  let le := lowerEnv cfg.mod env.vars results
  obtain ⟨ids, middle, afterCall, argsRun, definition, tail⟩ := lowerExpr_call_split
    (show lowerExpr (.call context (.byVal (.read place) :: rest) origin) le before =
      ((lowerExpr (.call context (.byVal (.read place) :: rest) origin) le before).1, (lowerExpr (.call context (.byVal (.read place) :: rest) origin) le before).2) from rfl)
  have afterExtended : ExtT afterCall caller.blocks := by
    rcases tail with ⟨_, term⟩ | ⟨_, rfl⟩
    · exact extended.of_adv (adv_emitTerm term)
    · exact extended
  have sameIds : ids = (lowerArgs (.byVal (.read place) :: rest) le before).1 := by rw [argsRun]
  have sameMiddle : middle = (lowerArgs (.byVal (.read place) :: rest) le before).2 := by rw [argsRun]
  subst ids
  subst middle
  have instruction := (emitDef_facts definition finalInput.atPoint afterExtended).2.2.2.2
  exact ⟨fuel, length, point, frame, values, evaluated, executed, wholePost, read, executed.reachable callerStart, instruction⟩


#print axioms accepted_generated_call_read_scalar_frontier
end Goose.Lower

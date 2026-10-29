import Goose.Lower.DemandCallSplitMixedArgumentsForward
import Goose.Lower.DemandCallSplitBooleanFrontier

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_call_split_mixed_frontier_forward {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {caller : Func} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod caller (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (form : SplitMixedArguments source.rootsEnv.access arguments) {initial : GIR.Frame} {start : Pt}
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results loop
      source.typingEnv source.rootsEnv before initial start)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (coverage : map.Covers required) (shrink : cfg.mod.profile = .shrink)
    {sourceFuel : Nat} {sourceValues : List Val} {sourceAfter : St}
    (sourceDone : mapList (evalArg sourceFuel cfg env) arguments state = .ok sourceValues sourceAfter)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    (callerStart : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state) :
    sourceAfter = state ∧ ∃ (length : Nat) (point : Pt) (frame : GIR.Frame),
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ length ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial
        (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2 frame point [] ∧
      mapList (getVal frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 state = .ok sourceValues state ∧
      RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point frame state ∧
      instAt caller point = some (.def (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1
        (.call context (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 (some origin))) := by
  obtain ⟨stateEq, length, point, frame, aliases, slots, executed, split, bound, carried, checked, wholePost, cells, read, finalInput⟩ :=
    accepted_generated_call_split_mixed_arguments_forward source occurrence rows form input admitted bounded realized coverage shrink sourceDone extended
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
  exact ⟨stateEq, length, point, frame, executed, wholePost, read, executed.reachable callerStart, instruction⟩


#print axioms accepted_generated_call_split_mixed_frontier_forward
end Goose.Lower

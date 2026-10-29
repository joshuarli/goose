import Goose.Lower.DemandCallInstructionShape
import Goose.Lower.DemandCallMixedStoppedCells

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

structure GeneratedCallFrontierAgreement {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    (caller : Func) (results : List Ty) (before : LS) (initial : GIR.Frame) (map : RetainedSsaMap) : Prop where
  stopped : ∀ {argumentFuel targetFuel : Nat} {values : List Val} {middle after : St} {frame : GIR.Frame} {point : Pt} {stop : Stop},
    mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle →
    Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial
      (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2 frame point [] →
    mapList (getVal frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 middle = .ok values middle →
    RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle →
    execOp targetFuel ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ frame
      (.call context (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 (some origin)) middle = .stop stop after →
    stop ≠ .timeout → ∃ sourceFuel, evalExpr sourceFuel cfg env (.call context arguments origin) state = .stop stop after
  successful : ∀ {argumentFuel targetFuel : Nat} {values : List Val} {middle after : St} {frame : GIR.Frame} {point : Pt} {value : Val},
    mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle →
    Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial
      (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2 frame point [] →
    mapList (getVal frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 middle = .ok values middle →
    RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle →
    execOp targetFuel ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ frame
      (.call context (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 (some origin)) middle = .ok (.val value) after →
    ∃ sourceFuel, evalExpr sourceFuel cfg env (.call context arguments origin) state = .ok value after ∧
      ExpressionDemandBoundary source map ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial
        (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2
        (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 value after
        (point.1, point.2 + 1) (frame.set (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.val value))

inductive StoppedCallArgumentsProgress {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    (caller : Func) (results : List Ty) (before : LS) (initial : GIR.Frame) (start : Pt)
    (taken : Nat) (reached : DemandRuntimePoint) (stop : Stop) (after : St) : Prop
  | aborted (trace : CallArgumentsStopped cfg env arguments state stop after) :
      StoppedCallArgumentsProgress source caller results before initial start taken reached stop after
  | complete {consumed remaining : Nat} {boundary : DemandRuntimePoint} {values : List Val}
      (count : consumed + remaining = taken)
      (executed : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ consumed ⟨start, initial, state⟩ boundary)
      (residual : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ remaining boundary reached)
      (trace : CallArgumentsDone cfg env arguments state values boundary.state)
      (post : Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial
        (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2 boundary.frame boundary.point [])
      (cells : CallArgumentCells (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 values
        (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2.vals.size boundary.frame)
      :
      StoppedCallArgumentsProgress source caller results before initial start taken reached stop after

theorem accepted_generated_call_stopped_from_frontier {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {caller : Func} {results : List Ty} {before : LS} {map : RetainedSsaMap}
    {initial : GIR.Frame} {start : Pt}
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    (agreement : GeneratedCallFrontierAgreement source caller results before initial map)
    (callerStart : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state)
    {taken : Nat} {reached : DemandRuntimePoint} {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ targetFuel reached stop after)
    (nonTimeout : stop ≠ .timeout)
    (argumentProgress : StoppedCallArgumentsProgress source caller results before initial start taken reached stop after) :
    StoppedExpressionPrefix source map ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results before initial start taken reached stop after := by
  let cx : FnCtx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩
  cases argumentProgress with
  | aborted trace =>
    obtain ⟨sourceFuel, done⟩ := trace.fuel.2
    apply StoppedExpressionPrefix.aborted (sourceFuel + 1)
    simp only [evalExpr, bind_apply, done]
  | @complete consumed remaining boundary values count argumentSteps residual trace wholePost cells =>
    obtain ⟨sourceFuel, argumentsDone⟩ := trace.fuel
    have read : mapList (getVal boundary.frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 boundary.state = .ok values boundary.state := by
      simpa using cells.read boundary.state
    have callPost : Post cfg env cx before initial (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2
        boundary.frame boundary.point [] := by simpa using wholePost
    have callerPoint : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller boundary.point boundary.frame boundary.state :=
      argumentSteps.reachable callerStart
    let le := lowerEnv cfg.mod env.vars results
    obtain ⟨ids, middle, afterCall, argsRun, definition, tail⟩ := lowerExpr_call_split
      (show lowerExpr (.call context arguments origin) le before =
        ((lowerExpr (.call context arguments origin) le before).1, (lowerExpr (.call context arguments origin) le before).2) from rfl)
    have afterExtended : ExtT afterCall caller.blocks := by
      rcases tail with ⟨_, term⟩ | ⟨_, rfl⟩
      · exact extended.of_adv (adv_emitTerm term)
      · exact extended
    have idsEq : ids = (lowerArgs arguments le before).1 := by rw [argsRun]
    have middleEq : middle = (lowerArgs arguments le before).2 := by rw [argsRun]
    subst ids
    subst middle
    obtain ⟨_, instruction⟩ := Post.def_leaf callPost definition afterExtended (.val .unit)
    rcases residual.uncons with ⟨_, same⟩ | ⟨rest, next, length, first, later⟩
    · subst reached
      cases stopped with
      | timeout => exact (nonTimeout rfl).elim
      | effect found execution => cases instruction.symm.trans found
      | definition found execution =>
        cases instruction.symm.trans found
        obtain ⟨sourceStopFuel, sourceStopped⟩ := agreement.stopped argumentsDone callPost read callerPoint execution nonTimeout
        exact .aborted sourceStopFuel sourceStopped
    · cases next
      cases first with
      | effect found execution => cases instruction.symm.trans found
      | branch found read enter => cases instruction.symm.trans found
      | branchTrue found test read enter => cases instruction.symm.trans found
      | branchFalse found test read enter => cases instruction.symm.trans found
      | define found execution =>
        cases instruction.symm.trans found
        obtain ⟨value, rfl⟩ := callOp_success_value execution
        obtain ⟨callFuel, evaluated, boundaryResult⟩ := agreement.successful argumentsDone callPost read callerPoint execution
        have callStep : RuntimeStep cx.cfg cx.fn boundary.point boundary.frame boundary.state
            (boundary.point.1, boundary.point.2 + 1)
            (boundary.frame.set (lowerExpr (.call context arguments origin) le before).1 (.val value)) _ :=
          .define instruction execution
        exact .complete (by omega) (argumentSteps.append (.next callStep (.zero _))) later evaluated boundaryResult


theorem accepted_generated_call_stopped_expression {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod caller (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results loop
      source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    (shrink : cfg.mod.profile = .shrink) (form : CallMixedStoppedArguments source.rootsEnv.access arguments)
    (agreement : GeneratedCallFrontierAgreement source caller results before initial map)
    (callerStart : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ targetFuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    StoppedExpressionPrefix source map ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results before initial start taken reached stop after := by
  have progress := accepted_generated_call_mixed_stopped_cells source selected owned occurrence rows coverage admitted bounded
    realized input extended shrink form steps stopped nonTimeout
  have shared : StoppedCallArgumentsProgress source caller results before initial start taken reached stop after := by
    cases progress with
    | aborted trace => exact .aborted trace
    | @complete consumed remaining boundary values prior count executed residual trace tracked argumentBounded argumentRealized post cells argumentInput =>
      exact .complete count executed residual trace (by simpa using post) (by simpa using cells)
  exact accepted_generated_call_stopped_from_frontier source extended agreement callerStart stopped nonTimeout shared

#print axioms accepted_generated_call_stopped_from_frontier
#print axioms accepted_generated_call_stopped_expression
end Goose.Lower

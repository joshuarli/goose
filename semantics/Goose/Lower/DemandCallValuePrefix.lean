import Goose.Lower.DemandCallValueSequence

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive CallValueArguments : List Arg → Prop
  | nil : CallValueArguments []
  | cons {expression : Expr} {rest : List Arg} (form : ControlPrefixExpression expression)
      (tail : CallValueArguments rest) : CallValueArguments (.byVal expression :: rest)

inductive CallValuePrefix {cfg : Cfg} {env : Env} {initialState : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    (cx : FnCtx) (results : List Ty) (before : LS) (loop : Option LoopCtx) (map required : RetainedSsaMap) :
    Nat → List Arg → DemandRuntimePoint → Nat → DemandRuntimePoint → Prop
  | interior {index : Nat} {expression : Expr} {rest : List Arg} {start reached : DemandRuntimePoint} {taken : Nat}
      (found : arguments[index]? = some (.byVal expression))
      (child : ExprSource cfg env expression start.state)
      (canonical : (ArgSource.byVal child).MatchesContext source.world source.typingEnv source.rootsEnv
        (callArgContext source.context index (.byVal expression) found))
      {prior : List (ValueId × RetainedAlias)}
      (cursor : GeneratedControlProgressCursor cx child
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2
        (lowerExpr expression (lowerEnv cfg.mod env.vars results)
          (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).2 start.frame start.point
        ⟨prior ++ map.values, map.runs⟩ ⟨prior ++ required.values, required.runs⟩ reached) :
      CallValuePrefix source cx results before loop map required index (.byVal expression :: rest) start taken reached
  | next {index : Nat} {expression : Expr} {rest : List Arg} {start boundary reached : DemandRuntimePoint}
      {taken consumed remaining fuel : Nat} {value : Val}
      (count : consumed + remaining = taken)
      (executed : DemandRuntimePrefix cx consumed start boundary)
      (evaluated : evalExpr fuel cfg env expression start.state = .ok value boundary.state)
      (tail : CallValuePrefix source cx results before loop map required (index + 1) rest boundary remaining reached) :
      CallValuePrefix source cx results before loop map required index (.byVal expression :: rest) start taken reached
  | complete {index : Nat} {start reached : DemandRuntimePoint} {taken : Nat}
      {prior : List (ValueId × RetainedAlias)}
      (steps : DemandRuntimePrefix cx taken start reached)
      (tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 prior)
      (bounded : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
      (realized : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env start)
      (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 start.frame start.point) :
      CallValuePrefix source cx results before loop map required index [] start taken reached

theorem accepted_generated_call_values_prefix_suffix {cfg : Cfg} {env : Env} {initialState : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (shrink : cfg.mod.profile = .shrink) {rest : List Arg} (form : CallValueArguments rest)
    {index : Nat} {state : St} (sources : ∀ fuel, ArgsSource fuel cfg env rest state)
    (canonical : ∀ fuel, (sources fuel).CallChildren source index)
    {prior : List (ValueId × RetainedAlias)}
    (tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 prior)
    {initial : GIR.Frame} {start : Pt}
    (bounded : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    : CallValuePrefix source cx results before loop map required index rest ⟨start, initial, state⟩ taken reached := by
  induction form generalizing index state initial start prior taken reached with
  | nil => exact .complete steps tracked bounded realized input
  | @cons expression rest headForm tailForm ih =>
    cases sourceEq : sources 0 with
    | cons head tail =>
      cases head with
      | byVal child =>
        have evidence := canonical 0
        rw [sourceEq] at evidence
        obtain ⟨found, childCanonical, _⟩ := evidence
        have stage := accepted_generated_call_value_stage source found child childCanonical selected owned occurrence rows tracked
          coverage admitted bounded realized input extended headForm steps
        cases stage with
        | interior cursor => exact .interior found child childCanonical cursor
        | @complete sourceFuel consumed remaining boundary value count executed residual evaluated post =>
          have done : evalArg (sourceFuel + 1) cfg env (.byVal expression) state = .ok value boundary.state := by
            simpa [evalArg] using evaluated
          obtain ⟨aliases, query⟩ := source.callArgumentAlias found shrink
          obtain ⟨nextTracked, nextRealized, nextBounded⟩ :=
            accepted_generated_call_value_finish source found child childCanonical tracked query post
          have nextInput := accepted_generated_call_value_next_input source found child input post
          let nextSources := ArgsSource.afterHead sources done
          have nextCanonical : ∀ fuel, (nextSources fuel).CallChildren source (index + 1) := by
            intro fuel
            exact ArgsSource.afterHead_callChildren source sources canonical done fuel
          have next := ih nextSources nextCanonical nextTracked nextBounded nextRealized nextInput residual
          exact .next count executed evaluated next

theorem accepted_generated_call_values_prefix {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (shrink : cfg.mod.profile = .shrink) (form : CallValueArguments arguments)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    : CallValuePrefix source cx results before loop map required 0 arguments ⟨start, initial, state⟩ taken reached := by
  let sources := fun fuel => Classical.choose (source.callArgsCanonical fuel results input.metadata)
  have canonical : ∀ fuel, (sources fuel).CallChildren source 0 := by
    intro fuel
    exact (Classical.choose_spec (source.callArgsCanonical fuel results input.metadata)).2
  have tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take 0)
      (lowerArgs (arguments.take 0) (lowerEnv cfg.mod env.vars results) before).1 [] := by
    simpa [lowerArgs, pure_run] using (GeneratedCallArgumentRows.nil (access := source.rootsEnv.access) (path := source.path) 0)
  apply accepted_generated_call_values_prefix_suffix source selected owned occurrence rows coverage admitted extended shrink form sources canonical tracked
  · simpa [lowerArgs, pure_run] using bounded
  · simpa using realized
  · simpa [lowerArgs, pure_run] using input
  · exact steps

#print axioms accepted_generated_call_values_prefix
#print axioms accepted_generated_call_values_prefix_suffix

end Goose.Lower

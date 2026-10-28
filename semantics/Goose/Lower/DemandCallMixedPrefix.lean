import Goose.Lower.DemandCallReferenceDemand
import Goose.Lower.DemandCallMixedStopped
import Goose.Lower.DemandCallValuePrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive CallMixedArguments (access : AccessEnv) : List Arg → Prop
  | nil : CallMixedArguments access []
  | value {expression : Expr} {rest : List Arg} (form : ControlPrefixExpression expression)
      (tail : CallMixedArguments access rest) : CallMixedArguments access (.byVal expression :: rest)
  | reference {mutability : Mutability} {place : Place} {rest : List Arg} (form : ScalarReadPlace place)
      (type : CallReferenceSupported access place)
      (tail : CallMixedArguments access rest) : CallMixedArguments access (.byRef mutability place :: rest)

inductive CallMixedPrefix {cfg : Cfg} {env : Env} {initialState : St}
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
      CallMixedPrefix source cx results before loop map required index (.byVal expression :: rest) start taken reached
  | next {index : Nat} {expression : Expr} {rest : List Arg} {start boundary reached : DemandRuntimePoint}
      {taken consumed remaining fuel : Nat} {value : Val}
      (count : consumed + remaining = taken)
      (executed : DemandRuntimePrefix cx consumed start boundary)
      (evaluated : evalExpr fuel cfg env expression start.state = .ok value boundary.state)
      (tail : CallMixedPrefix source cx results before loop map required (index + 1) rest boundary remaining reached) :
      CallMixedPrefix source cx results before loop map required index (.byVal expression :: rest) start taken reached
  | referenceInterior {index : Nat} {mutability : Mutability} {place : Place} {rest : List Arg}
      {start reached boundary : DemandRuntimePoint} {taken length remaining : Nat} {location : Loc}
      (found : arguments[index]? = some (.byRef mutability place))
      (child : PlaceSource cfg env place start.state) (target : child.ty.refTarget = true)
      (canonical : (ArgSource.byRef mutability child (Or.inl target)).MatchesContext source.world source.typingEnv source.rootsEnv
        (callArgContext source.context index (.byRef mutability place) found))
      {prior : List (ValueId × RetainedAlias)}
      (placeEntry : DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.inputFuture
        (prior ++ map.values) map.runs start)
      (placeAddressed : DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        (prior ++ map.values) map.runs
        ⟨(start.point.1, start.point.2 + 1), start.frame.set (lowerPlace place (lowerEnv cfg.mod env.vars results)
          (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1 (.val (.ref location)), start.state⟩)
      (currentDemand : DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.inputFuture
          (prior ++ map.values) map.runs reached ∨
        DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
          (prior ++ map.values) map.runs reached)
      (same : Same (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size
        start.frame reached.frame)
      (evaluated : evalArg 2 cfg env (.byRef mutability place) start.state = .ok (.ref location) boundary.state)
      (expected : DemandRuntimePrefix cx length start boundary)
      (count : taken + remaining = length)
      (suffix : DemandRuntimePrefix cx remaining reached boundary) :
      CallMixedPrefix source cx results before loop map required index (.byRef mutability place :: rest) start taken reached
  | referenceNext {index : Nat} {mutability : Mutability} {place : Place} {rest : List Arg}
      {start boundary reached : DemandRuntimePoint} {taken consumed remaining : Nat} {location : Loc}
      (count : consumed + remaining = taken)
      (executed : DemandRuntimePrefix cx consumed start boundary)
      (evaluated : evalArg 2 cfg env (.byRef mutability place) start.state = .ok (.ref location) boundary.state)
      (tail : CallMixedPrefix source cx results before loop map required (index + 1) rest boundary remaining reached) :
      CallMixedPrefix source cx results before loop map required index (.byRef mutability place :: rest) start taken reached
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
      CallMixedPrefix source cx results before loop map required index [] start taken reached

theorem accepted_generated_call_mixed_prefix_suffix {cfg : Cfg} {env : Env} {initialState : St}
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
    (shrink : cfg.mod.profile = .shrink) {rest : List Arg} (form : CallMixedArguments source.rootsEnv.access rest)
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
    : CallMixedPrefix source cx results before loop map required index rest ⟨start, initial, state⟩ taken reached := by
  induction form generalizing index state initial start prior taken reached with
  | nil => exact .complete steps tracked bounded realized input
  | @value expression rest headForm tailForm ih =>
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
  | @reference mutability place rest headForm typeFact tailForm ih =>
    cases sourceEq : sources 0 with
    | cons head tail =>
      cases head with
      | byRef _ child allowed =>
        have evidence := canonical 0
        rw [sourceEq] at evidence
        obtain ⟨found, childCanonical, _⟩ := evidence
        obtain ⟨plans, path, world, typing, roots, childContext⟩ := childCanonical
        have accessType := tyPlace_accessType (child.frame.mod_t.trans child.frame.mod_p.symm)
          (child.frame.vars_t.trans child.frame.vars_p.symm) child.typed
        rw [roots] at accessType
        have target : child.ty.refTarget = true := CallReferenceSupported.target typeFact accessType allowed
        have childCanonical : (ArgSource.byRef mutability child (Or.inl target)).MatchesContext
            source.world source.typingEnv source.rootsEnv (callArgContext source.context index (.byRef mutability place) found) :=
          ⟨plans, path, world, typing, roots, childContext⟩
        obtain ⟨location, length, point, frame, aliases, done, traversal, first, tail, finalPost, nextTracked, nextRealized, nextBounded, nextInput⟩ :=
          accepted_generated_call_reference_complete_demand source found child target childCanonical headForm occurrence rows tracked
            bounded realized input extended
        have executed := DemandRuntimePrefix.next ((first 0).runtime) tail
        rcases executed.compare steps with ⟨remaining, count, residual⟩ | ⟨remaining, count, suffix⟩
        · let nextSources := ArgsSource.afterHead sources done
          have nextCanonical : ∀ fuel, (nextSources fuel).CallChildren source (index + 1) := by
            intro fuel
            exact ArgsSource.afterHead_callChildren source sources canonical done fuel
          have next := ih nextSources nextCanonical nextTracked nextBounded nextRealized nextInput residual
          exact .referenceNext count executed done next
        · obtain ⟨actualLocation, placed, placeEntry, placeAddressed, addressStep⟩ :=
            accepted_generated_call_reference_demand source found child (Or.inl target) childCanonical headForm occurrence rows tracked
              input.atPoint input.related bounded realized extended
          have locationEq : actualLocation = location := by
            have same := done
            simp [evalArg, bind_apply, placed, pure_apply] at same
            exact same
          subst actualLocation
          have currentDemand := traversal.runtimePrefix_invariant (by omega) steps
          exact .referenceInterior found child target childCanonical placeEntry placeAddressed currentDemand.1 currentDemand.2 done executed count suffix

theorem accepted_generated_call_mixed_prefix {cfg : Cfg} {env : Env} {state : St}
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
    (shrink : cfg.mod.profile = .shrink) (form : CallMixedArguments source.rootsEnv.access arguments)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    : CallMixedPrefix source cx results before loop map required 0 arguments ⟨start, initial, state⟩ taken reached := by
  let sources := fun fuel => Classical.choose (source.callArgsCanonical fuel results input.metadata)
  have canonical : ∀ fuel, (sources fuel).CallChildren source 0 := by
    intro fuel
    exact (Classical.choose_spec (source.callArgsCanonical fuel results input.metadata)).2
  have tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take 0)
      (lowerArgs (arguments.take 0) (lowerEnv cfg.mod env.vars results) before).1 [] := by
    simpa [lowerArgs, pure_run] using (GeneratedCallArgumentRows.nil (access := source.rootsEnv.access) (path := source.path) 0)
  apply accepted_generated_call_mixed_prefix_suffix source selected owned occurrence rows coverage admitted extended shrink form sources canonical tracked
  · simpa [lowerArgs, pure_run] using bounded
  · simpa using realized
  · simpa [lowerArgs, pure_run] using input
  · exact steps

#print axioms accepted_generated_call_mixed_prefix
end Goose.Lower

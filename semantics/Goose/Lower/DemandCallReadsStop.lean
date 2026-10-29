import Goose.Lower.DemandCallReadsSequence
import Goose.Lower.DemandCallSplitReadStop

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_generated_call_reads_stop {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {rest : List Arg} (form : ScalarReadArguments rest)
    {index : Nat} (sources : ∀ fuel, ArgsSource fuel cfg env rest state)
    (canonical : ∀ fuel, (sources fuel).CallChildren source index)
    {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell} {map : RetainedSsaMap}
    (readAdmitted : map.Admitted cfg.mod.profile source.context.retained)
    (coverage : map.Covers required)
    (shrink : cfg.mod.profile = .shrink)
    (split : SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 values slots)
    {initial : GIR.Frame} {start : Pt}
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    (bounded : (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Bounded
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Realizes
      cfg.mod source.world env ⟨start, initial, state⟩)
    (checked : ∀ cell ∈ slots, cell.Checked source index initial)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {runtime : DemandRuntimePoint} (unfinished : taken < 2 * rest.length)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ runtime)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel runtime stop after) (nonTimeout : stop ≠ .timeout) :
    CallArgumentsStopped cfg env rest state stop after := by
  induction form generalizing index initial start values slots taken runtime with
  | nil => simp at unfinished
  | @read place rest readForm tail ih =>
    cases sourceEq : sources 0 with
    | cons head tailSource =>
      cases head with
      | byVal child =>
        have evidence := canonical 0
        rw [sourceEq] at evidence
        obtain ⟨found, childCanonical, _⟩ := evidence
        by_cases early : taken < 2
        · exact .head (accepted_generated_call_split_read_stop source found child readForm childCanonical
            occurrence rows coverage split realized input extended early steps stopped nonTimeout) nonTimeout
        · have enough : 2 ≤ taken := by omega
          obtain ⟨middle, aliases, value, leading, residual, evaluated, sameState, post, nextRows,
            nextRealized, nextBounded, nextChecked, nextInput⟩ :=
            accepted_generated_call_split_read_prefix_post source found child readForm childCanonical occurrence rows coverage split
              realized readAdmitted bounded input extended shrink checked enough steps
          cases middle with
          | mk point frame nextState =>
            simp only at sameState
            subst nextState
            let nextSources := ArgsSource.afterHead sources evaluated
            have nextCanonical : ∀ fuel, (nextSources fuel).CallChildren source (index + 1) := by
              intro fuel
              exact ArgsSource.afterHead_callChildren source sources canonical evaluated fuel
            have tailUnfinished : taken - 2 < 2 * rest.length := by simp only [List.length_cons] at unfinished; omega
            exact .tail evaluated (ih nextSources nextCanonical nextRows nextInput nextBounded nextRealized nextChecked
              tailUnfinished residual stopped)

#print axioms accepted_generated_call_reads_stop
end Goose.Lower

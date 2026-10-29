import Goose.Lower.DemandCallSplitMixedForward

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_generated_call_split_mixed_arguments_forward {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (form : SplitMixedArguments source.rootsEnv.access arguments) {initial : GIR.Frame} {start : Pt}
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (coverage : map.Covers required) (shrink : cfg.mod.profile = .shrink)
    {sourceFuel : Nat} {sourceValues : List Val} {sourceAfter : St}
    (sourceDone : mapList (evalArg sourceFuel cfg env) arguments state = .ok sourceValues sourceAfter)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    sourceAfter = state ∧ ∃ (length : Nat) (point : Pt) (frame : GIR.Frame)
      (aliases : List (ValueId × RetainedAlias)) (slots : List SliceSlotArgumentCell),
      DemandRuntimePrefix cx length ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      SplitCallArgumentRows source.rootsEnv.access source.path 0 arguments
        (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 aliases slots ∧
      (⟨⟨aliases ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Bounded
        (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      (⟨⟨aliases ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Realizes cfg.mod source.world env ⟨point, frame, state⟩ ∧
      (∀ cell ∈ slots, cell.Checked source arguments.length frame) ∧
      Post cfg env cx before initial (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2 frame point [] ∧
      CallArgumentCells (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 sourceValues
        (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2.vals.size frame ∧
      mapList (getVal frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 state = .ok sourceValues state ∧
      GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
        (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2 frame point := by
  let sources := fun fuel => Classical.choose (source.callArgsCanonical fuel results input.metadata)
  have canonical : ∀ fuel, (sources fuel).CallChildren source 0 := by
    intro fuel
    exact (Classical.choose_spec (source.callArgsCanonical fuel results input.metadata)).2
  have split : SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take 0)
      (lowerArgs (arguments.take 0) (lowerEnv cfg.mod env.vars results) before).1 [] [] := by
    simpa [lowerArgs, pure_run] using (SplitCallArgumentRows.nil (access := source.rootsEnv.access) (path := source.path) 0)
  have input' : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take 0) (lowerEnv cfg.mod env.vars results) before).2 initial start := by
    simpa [lowerArgs, pure_run] using input
  have bounded' : (⟨⟨[] ++ map.values, map.runs⟩, []⟩ : SplitCallRetained).Bounded
      (lowerArgs (arguments.take 0) (lowerEnv cfg.mod env.vars results) before).2.vals.size := by
    simpa [SplitCallRetained.Bounded, lowerArgs, pure_run] using bounded
  have realized' : (⟨⟨[] ++ map.values, map.runs⟩, []⟩ : SplitCallRetained).Realizes
      cfg.mod source.world env ⟨start, initial, state⟩ := by
    exact ⟨by simpa using realized, by simp [SliceSlotArgumentCells.Realizes]⟩
  have cells : CallArgumentCells (lowerArgs (arguments.take 0) (lowerEnv cfg.mod env.vars results) before).1 []
      (lowerArgs (arguments.take 0) (lowerEnv cfg.mod env.vars results) before).2.vals.size initial := by
    simpa [lowerArgs, pure_run] using CallArgumentCells.empty before.vals.size initial
  have wholePost : Post cfg env cx before initial
      (lowerArgs (arguments.take 0) (lowerEnv cfg.mod env.vars results) before).2 initial start [] := by
    simpa [lowerArgs, pure_run] using Post.init input.related input.atPoint
  obtain ⟨length, point, frame, values, slots, valuesEq, stateEq, trace, executed, aliases, rowsFinal,
    boundFinal, realizedFinal, checkedFinal, postFinal, cellsFinal, inputFinal⟩ :=
    accepted_generated_call_split_mixed_forward source occurrence rows form sources canonical admitted coverage shrink
      (CallArgumentsDone.of_mapList sourceDone) split wholePost cells input' bounded' realized' (by simp) extended
  subst values
  refine ⟨stateEq, length, point, frame, aliases, slots, executed, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using rowsFinal
  · simpa using boundFinal
  · simpa using realizedFinal
  · simpa using checkedFinal
  · simpa using postFinal
  · simpa using cellsFinal
  · simpa using cellsFinal.read state
  · simpa using inputFinal

#print axioms accepted_generated_call_split_mixed_arguments_forward
end Goose.Lower

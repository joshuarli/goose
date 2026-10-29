import Goose.Lower.DemandCallReadScalarSequence

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_generated_call_read_scalar_arguments {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {place : Place} {rest : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context (.byVal (.read place) :: rest) origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context (.byVal (.read place) :: rest) origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (readForm : ScalarReadPlace place) (form : LocalSliceScalarArguments source.rootsEnv.access rest) {initial : GIR.Frame} {start : Pt}
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (coverage : map.Covers required)
    (shrink : cfg.mod.profile = .shrink)
    (extended : ExtT (lowerExpr (.call context (.byVal (.read place) :: rest) origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {runtime : DemandRuntimePoint} (completed : 2 ≤ taken)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ runtime) :
    ∃ (fuel length : Nat) (point : Pt) (frame : GIR.Frame) (values : List Val) (aliases : List (ValueId × RetainedAlias)) (slots : List SliceSlotArgumentCell),
      mapList (evalArg fuel cfg env) (.byVal (.read place) :: rest) state = .ok values state ∧
      DemandRuntimePrefix cx length ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      SplitCallArgumentRows source.rootsEnv.access source.path 0 (.byVal (.read place) :: rest)
        (lowerArgs (.byVal (.read place) :: rest) (lowerEnv cfg.mod env.vars results) before).1 aliases slots ∧
      (⟨⟨aliases ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Bounded
        (lowerArgs (.byVal (.read place) :: rest) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      (⟨⟨aliases ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Realizes cfg.mod source.world env ⟨point, frame, state⟩ ∧
      (∀ cell ∈ slots, cell.Checked source (.byVal (.read place) :: rest).length frame) ∧
      Post cfg env cx before initial (lowerArgs (.byVal (.read place) :: rest) (lowerEnv cfg.mod env.vars results) before).2 frame point [] ∧
      CallArgumentCells (lowerArgs (.byVal (.read place) :: rest) (lowerEnv cfg.mod env.vars results) before).1 values
        (lowerArgs (.byVal (.read place) :: rest) (lowerEnv cfg.mod env.vars results) before).2.vals.size frame ∧
      mapList (getVal frame) (lowerArgs (.byVal (.read place) :: rest) (lowerEnv cfg.mod env.vars results) before).1 state = .ok values state ∧
      GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
        (lowerArgs (.byVal (.read place) :: rest) (lowerEnv cfg.mod env.vars results) before).2 frame point := by
  let sources := fun fuel => Classical.choose (source.callArgsCanonical fuel results input.metadata)
  have canonical : ∀ fuel, (sources fuel).CallChildren source 0 := by
    intro fuel
    exact (Classical.choose_spec (source.callArgsCanonical fuel results input.metadata)).2
  have split : SplitCallArgumentRows source.rootsEnv.access source.path 0 ((.byVal (.read place) :: rest).take 0)
      (lowerArgs ((.byVal (.read place) :: rest).take 0) (lowerEnv cfg.mod env.vars results) before).1 [] [] := by
    simpa [lowerArgs, pure_run] using (SplitCallArgumentRows.nil (access := source.rootsEnv.access) (path := source.path) 0)
  have input' : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs ((.byVal (.read place) :: rest).take 0) (lowerEnv cfg.mod env.vars results) before).2 initial start := by
    simpa [lowerArgs, pure_run] using input
  have bounded' : (⟨⟨[] ++ map.values, map.runs⟩, []⟩ : SplitCallRetained).Bounded
      (lowerArgs ((.byVal (.read place) :: rest).take 0) (lowerEnv cfg.mod env.vars results) before).2.vals.size := by
    simpa [SplitCallRetained.Bounded, lowerArgs, pure_run] using bounded
  have realized' : (⟨⟨[] ++ map.values, map.runs⟩, []⟩ : SplitCallRetained).Realizes
      cfg.mod source.world env ⟨start, initial, state⟩ := by
    exact ⟨by simpa using realized, by simp [SliceSlotArgumentCells.Realizes]⟩
  have cells : CallArgumentCells (lowerArgs ((.byVal (.read place) :: rest).take 0) (lowerEnv cfg.mod env.vars results) before).1 []
      (lowerArgs ((.byVal (.read place) :: rest).take 0) (lowerEnv cfg.mod env.vars results) before).2.vals.size initial := by
    simpa [lowerArgs, pure_run] using CallArgumentCells.empty before.vals.size initial
  have wholePost : Post cfg env cx before initial
      (lowerArgs ((.byVal (.read place) :: rest).take 0) (lowerEnv cfg.mod env.vars results) before).2 initial start [] := by
    simpa [lowerArgs, pure_run] using Post.init input.related input.atPoint
  obtain ⟨length, point, frame, values, aliases, slots, done, executed, rowsFinal, boundFinal, realizedFinal,
    checkedFinal, postFinal, cellsFinal, inputFinal⟩ :=
    accepted_generated_call_read_scalar_sequence source occurrence rows readForm form sources canonical admitted coverage shrink
      (fun _ _ _ _ _ => admitted) split wholePost cells input' bounded' realized' (by simp) extended completed steps
  obtain ⟨fuel, evaluated⟩ := done.fuel
  refine ⟨fuel, length, point, frame, values, aliases, slots, evaluated, executed, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_comm] using rowsFinal
  · simpa [Nat.add_comm] using boundFinal
  · simpa [Nat.add_comm] using realizedFinal
  · simpa [Nat.add_comm] using checkedFinal
  · simpa [Nat.add_comm] using postFinal
  · simpa [Nat.add_comm] using cellsFinal
  · simpa [Nat.add_comm] using cellsFinal.read state
  · simpa [Nat.add_comm] using inputFinal

#print axioms accepted_generated_call_read_scalar_arguments
end Goose.Lower

import Goose.Lower.DemandCallReadState
import Goose.Lower.DemandCallSplitBooleanSequence

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_generated_call_read_scalar_sequence {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {place : Place} (readForm : ScalarReadPlace place)
    {rest : List Arg} (form : LocalSliceScalarArguments source.rootsEnv.access rest)
    {index : Nat} (sources : ∀ fuel, ArgsSource fuel cfg env (.byVal (.read place) :: rest) state)
    (canonical : ∀ fuel, (sources fuel).CallChildren source index)
    {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell} {map : RetainedSsaMap}
    (readAdmitted : map.Admitted cfg.mod.profile source.context.retained)
    (coverage : map.Covers required)
    (shrink : cfg.mod.profile = .shrink)
    (admitted : ∀ expression value operation, CallScalarLiteral expression value operation →
      .byVal expression ∈ rest → map.Admitted cfg.mod.profile source.context.retained)
    (split : SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 values slots)
    {initial rootFrame : GIR.Frame} {start : Pt} {previousValues : List Val}
    (wholePost : Post cfg env cx before rootFrame
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start [])
    (cells : CallArgumentCells (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 previousValues
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size initial)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    (bounded : (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Bounded
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Realizes
      cfg.mod source.world env ⟨start, initial, state⟩)
    (checked : ∀ cell ∈ slots, cell.Checked source index initial)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {runtime : DemandRuntimePoint} (completed : 2 ≤ taken)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ runtime) :
    ∃ (length : Nat) (point : Pt) (frame : GIR.Frame) (resultsValues : List Val)
      (finalValues : List (ValueId × RetainedAlias)) (finalSlots : List SliceSlotArgumentCell),
      CallArgumentsDone cfg env (.byVal (.read place) :: rest) state resultsValues state ∧
      DemandRuntimePrefix cx length ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take (index + 1 + rest.length))
        (lowerArgs (arguments.take (index + 1 + rest.length)) (lowerEnv cfg.mod env.vars results) before).1 finalValues finalSlots ∧
      (⟨⟨finalValues ++ map.values, map.runs⟩, finalSlots⟩ : SplitCallRetained).Bounded
        (lowerArgs (arguments.take (index + 1 + rest.length)) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      (⟨⟨finalValues ++ map.values, map.runs⟩, finalSlots⟩ : SplitCallRetained).Realizes
        cfg.mod source.world env ⟨point, frame, state⟩ ∧
      (∀ cell ∈ finalSlots, cell.Checked source (index + 1 + rest.length) frame) ∧
      Post cfg env cx before rootFrame
        (lowerArgs (arguments.take (index + 1 + rest.length)) (lowerEnv cfg.mod env.vars results) before).2 frame point [] ∧
      CallArgumentCells (lowerArgs (arguments.take (index + 1 + rest.length)) (lowerEnv cfg.mod env.vars results) before).1
        (previousValues ++ resultsValues) (lowerArgs (arguments.take (index + 1 + rest.length)) (lowerEnv cfg.mod env.vars results) before).2.vals.size frame ∧
      GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
        (lowerArgs (arguments.take (index + 1 + rest.length)) (lowerEnv cfg.mod env.vars results) before).2 frame point := by
  cases sourceEq : sources 0 with
  | cons head tailSource =>
    cases head with
    | byVal child =>
      have evidence := canonical 0
      rw [sourceEq] at evidence
      obtain ⟨found, childCanonical, _⟩ := evidence
      obtain ⟨middle, aliases, value, leading, residual, evaluated, sameState, post, nextRows,
        nextRealized, nextBounded, nextChecked, nextInput⟩ :=
        accepted_generated_call_split_read_prefix_post source found child readForm childCanonical occurrence rows coverage split
          realized readAdmitted bounded input extended shrink checked completed steps
      cases middle with
      | mk point frame after =>
        simp only at sameState
        subst after
        let id := (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results)
          (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1
        let newValues := values ++ aliases.map (fun alias => (id, alias))
        have nextCells := cells.next found post
        have nextPost : Post cfg env cx before rootFrame
            (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2 frame point [] := by
          have combined := wholePost.comp post
          have takeEq : arguments.take (index + 1) = arguments.take index ++ [.byVal (.read place)] := by
            rw [List.take_add_one, found]
            simp
          rw [takeEq, lowerArgs_append_run]
          simpa [lowerArgs, lowerArg, bind_run, pure_run] using combined.sub (by simp)
        let nextSources := ArgsSource.afterHead sources evaluated
        have nextCanonical : ∀ fuel, (nextSources fuel).CallChildren source (index + 1) := by
          intro fuel
          exact ArgsSource.afterHead_callChildren source sources canonical evaluated fuel
        obtain ⟨tailLength, finalPoint, finalFrame, finalValues, finalSlots, done, tailSteps, finalRows,
          finalBounded, finalRealized, finalChecked, finalPost, finalCells, finalInput⟩ :=
          accepted_generated_call_slice_scalar_sequence source occurrence rows form nextSources nextCanonical admitted
            nextRows nextPost nextCells nextInput nextBounded nextRealized nextChecked extended
        exact ⟨2 + tailLength, finalPoint, finalFrame, value :: finalValues, newValues, finalSlots,
          .cons evaluated done, leading.append tailSteps, finalRows, finalBounded, finalRealized, finalChecked,
          finalPost, by simpa [List.append_assoc] using finalCells, finalInput⟩

#print axioms accepted_generated_call_read_scalar_sequence
end Goose.Lower

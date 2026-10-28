import Goose.Lower.DemandCallSliceSequenceStage
import Goose.Lower.DemandCallFuel

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive LocalSliceArguments (access : AccessEnv) : List Arg → Prop
  | nil : LocalSliceArguments access []
  | cons {borrow : Mutability} {slot : VarId} {mutability : Mutability} {element : Ty} {rest : List Arg}
      (type : access.placeType? (.var slot) = some (.slice mutability element))
      (tail : LocalSliceArguments access rest) : LocalSliceArguments access (.byRef borrow (.var slot) :: rest)

theorem accepted_generated_call_slice_sequence {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {rest : List Arg} (form : LocalSliceArguments source.rootsEnv.access rest)
    {index : Nat} (sources : ∀ fuel, ArgsSource fuel cfg env rest state)
    (canonical : ∀ fuel, (sources fuel).CallChildren source index)
    {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell} {map : RetainedSsaMap}
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
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (length : Nat) (point : Pt) (frame : GIR.Frame) (resultsValues : List Val) (finalSlots : List SliceSlotArgumentCell),
      CallArgumentsDone cfg env rest state resultsValues state ∧
      DemandRuntimePrefix cx length ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take (index + rest.length))
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).1 values finalSlots ∧
      (⟨⟨values ++ map.values, map.runs⟩, finalSlots⟩ : SplitCallRetained).Bounded
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      (⟨⟨values ++ map.values, map.runs⟩, finalSlots⟩ : SplitCallRetained).Realizes
        cfg.mod source.world env ⟨point, frame, state⟩ ∧
      (∀ cell ∈ finalSlots, cell.Checked source (index + rest.length) frame) ∧
      GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).2 frame point := by
  induction form generalizing index initial start slots with
  | nil =>
    exact ⟨0, start, initial, [], slots, .nil state, .zero _, by simpa using split, by simpa using bounded,
      realized, by simpa using checked, by simpa using input⟩
  | @cons borrow slot mutability element rest type tail ih =>
    cases sourceEq : sources 0 with
    | cons head tailSource =>
      cases head with
      | byRef _ child target =>
        have evidence := canonical 0
        rw [sourceEq] at evidence
        obtain ⟨found, childCanonical, _⟩ := evidence
        have metadata := childCanonical
        obtain ⟨_, _, _, _, roots, _⟩ := metadata
        have accessType := tyPlace_accessType (child.frame.mod_t.trans child.frame.mod_p.symm)
          (child.frame.vars_t.trans child.frame.vars_p.symm) child.typed
        rw [roots, type] at accessType
        have childType : child.ty = .slice mutability element := (Option.some.inj accessType).symm
        obtain ⟨location, length, point, frame, cell, evaluated, executed, post, nextRows, nextBounded, nextRealized, nextChecked, nextInput⟩ :=
          accepted_generated_call_slice_sequence_stage source found child target childCanonical childType occurrence rows split input bounded realized checked extended
        let nextSources := ArgsSource.afterHead sources evaluated
        have nextCanonical : ∀ fuel, (nextSources fuel).CallChildren source (index + 1) := by
          intro fuel
          exact ArgsSource.afterHead_callChildren source sources canonical evaluated fuel
        obtain ⟨tailLength, finalPoint, finalFrame, finalValues, finalSlots, done, tailSteps, finalRows,
          finalBounded, finalRealized, finalChecked, finalInput⟩ :=
          ih nextSources nextCanonical nextRows nextInput nextBounded nextRealized nextChecked
        refine ⟨length + tailLength, finalPoint, finalFrame, .ref location :: finalValues, finalSlots,
          .cons evaluated done, executed.append tailSteps, ?_, ?_, finalRealized, ?_, ?_⟩
        · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalRows
        · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalBounded
        · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalChecked
        · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalInput

theorem accepted_generated_call_slice_arguments {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (form : LocalSliceArguments source.rootsEnv.access arguments) {initial : GIR.Frame} {start : Pt}
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (fuel length : Nat) (point : Pt) (frame : GIR.Frame) (values : List Val) (slots : List SliceSlotArgumentCell),
      mapList (evalArg fuel cfg env) arguments state = .ok values state ∧
      DemandRuntimePrefix cx length ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      SplitCallArgumentRows source.rootsEnv.access source.path 0 arguments
        (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 [] slots ∧
      (⟨map, slots⟩ : SplitCallRetained).Bounded
        (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      (⟨map, slots⟩ : SplitCallRetained).Realizes cfg.mod source.world env ⟨point, frame, state⟩ ∧
      (∀ cell ∈ slots, cell.Checked source arguments.length frame) ∧
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
  obtain ⟨length, point, frame, values, slots, done, executed, rowsFinal, boundFinal, realizedFinal, checkedFinal, inputFinal⟩ :=
    accepted_generated_call_slice_sequence source occurrence rows form sources canonical split input' bounded' realized'
      (by simp) extended
  obtain ⟨fuel, evaluated⟩ := done.fuel
  refine ⟨fuel, length, point, frame, values, slots, evaluated, executed, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using rowsFinal
  · simpa using boundFinal
  · simpa using realizedFinal
  · simpa using checkedFinal
  · simpa using inputFinal

#print axioms accepted_generated_call_slice_arguments

#print axioms accepted_generated_call_slice_sequence
end Goose.Lower

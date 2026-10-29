import Goose.Lower.DemandCallSplitReadForward
import Goose.Lower.DemandCallSplitMixedStop
import Goose.Lower.DemandScalarReadFuel

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem CallArgumentsDone.of_mapList {cfg : Cfg} {env : Env} {arguments : List Arg} {state after : St}
    {values : List Val} {fuel : Nat}
    (evaluated : mapList (evalArg fuel cfg env) arguments state = .ok values after) :
    CallArgumentsDone cfg env arguments state values after := by
  induction arguments generalizing state values after with
  | nil =>
    simp only [mapList, pure_apply, Res.ok.injEq] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    exact .nil _
  | cons argument rest ih =>
    simp only [mapList, bind_apply] at evaluated
    cases head : evalArg fuel cfg env argument state with
    | stop stop stopped => simp [head] at evaluated
    | ok value middle =>
      simp only [head] at evaluated
      cases tail : mapList (evalArg fuel cfg env) rest middle with
      | stop stop stopped => simp [tail] at evaluated
      | ok tailValues tailState =>
        simp only [tail, pure_apply, Res.ok.injEq] at evaluated
        obtain ⟨rfl, rfl⟩ := evaluated
        exact .cons head (ih tail)

#print axioms CallArgumentsDone.of_mapList

theorem accepted_generated_call_split_mixed_forward {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {rest : List Arg} (form : SplitMixedArguments source.rootsEnv.access rest)
    {index : Nat} (sources : ∀ fuel, ArgsSource fuel cfg env rest state)
    (canonical : ∀ fuel, (sources fuel).CallChildren source index)
    {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell} {map : RetainedSsaMap}
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (coverage : map.Covers required) (shrink : cfg.mod.profile = .shrink)
    {sourceValues : List Val} {sourceAfter : St} (sourceDone : CallArgumentsDone cfg env rest state sourceValues sourceAfter)
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
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (length : Nat) (point : Pt) (frame : GIR.Frame) (resultsValues : List Val) (finalSlots : List SliceSlotArgumentCell),
      resultsValues = sourceValues ∧ sourceAfter = state ∧
      CallArgumentsDone cfg env rest state resultsValues state ∧
      DemandRuntimePrefix cx length ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      ∃ finalAliases : List (ValueId × RetainedAlias),
      SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take (index + rest.length))
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).1 finalAliases finalSlots ∧
      (⟨⟨finalAliases ++ map.values, map.runs⟩, finalSlots⟩ : SplitCallRetained).Bounded
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      (⟨⟨finalAliases ++ map.values, map.runs⟩, finalSlots⟩ : SplitCallRetained).Realizes
        cfg.mod source.world env ⟨point, frame, state⟩ ∧
      (∀ cell ∈ finalSlots, cell.Checked source (index + rest.length) frame) ∧
      Post cfg env cx before rootFrame
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).2 frame point [] ∧
      CallArgumentCells (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).1
        (previousValues ++ resultsValues) (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).2.vals.size frame ∧
      GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).2 frame point := by
  induction form generalizing index state initial start values slots previousValues sourceValues sourceAfter with
  | nil =>
    cases sourceDone
    exact ⟨0, start, initial, [], slots, rfl, rfl, .nil state, .zero _, values, by simpa using split, by simpa using bounded,
      realized, by simpa using checked, by simpa using wholePost, by simpa using cells, by simpa using input⟩
  | @read place rest readForm tail ih =>
    cases sourceDone with
    | @cons argument sourceRest sourceState middle sourceEnd sourceValue sourceVals sourceFuel sourceEvaluated sourceTail =>
      cases sourceEq : sources 0 with
      | cons head tailSource =>
        cases head with
        | byVal child =>
          have evidence := canonical 0
          rw [sourceEq] at evidence
          obtain ⟨found, childCanonical, _⟩ := evidence
          have normalized := scalar_read_argument_success_fuel readForm sourceEvaluated
          obtain ⟨sameState, boundary, aliases, executed, boundaryState, post, nextRows, nextRealized,
            nextBounded, nextChecked, nextInput⟩ :=
            accepted_generated_call_split_read_forward source found child readForm childCanonical occurrence rows coverage split
              realized admitted bounded input extended shrink checked normalized
          subst middle
          cases boundary with
          | mk point frame nextState =>
            simp only at boundaryState
            subst nextState
            have nextCells := cells.next found post
            have nextPost : Post cfg env cx before rootFrame
                (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2 frame point [] := by
              have combined := wholePost.comp post
              have takeEq : arguments.take (index + 1) = arguments.take index ++ [.byVal (.read place)] := by
                rw [List.take_add_one, found]
                simp
              rw [takeEq, lowerArgs_append_run]
              simpa [lowerArgs, lowerArg, bind_run, pure_run] using combined.sub (by simp)
            let nextSources := ArgsSource.afterHead sources normalized
            have nextCanonical : ∀ fuel, (nextSources fuel).CallChildren source (index + 1) := by
              intro fuel
              exact ArgsSource.afterHead_callChildren source sources canonical normalized fuel
            obtain ⟨tailLength, finalPoint, finalFrame, finalValues, finalSlots, valuesEq, afterEq, done, tailSteps, finalAliases, finalRows,
              finalBounded, finalRealized, finalChecked, finalPost, finalCells, finalInput⟩ :=
              ih nextSources nextCanonical sourceTail nextRows nextPost nextCells nextInput nextBounded nextRealized nextChecked
            refine ⟨2 + tailLength, finalPoint, finalFrame, sourceValue :: finalValues, finalSlots,
              by simp [valuesEq], afterEq, .cons normalized done, executed.append tailSteps, finalAliases, ?_, ?_, finalRealized, ?_, ?_, ?_, ?_⟩
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalRows
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalBounded
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalChecked
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPost
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.append_assoc] using finalCells
            · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalInput
  | @literal expression value operation rest literal tail ih =>
    cases sourceDone with
    | @cons argument sourceRest sourceState middle sourceEnd sourceValue sourceVals sourceFuel sourceEvaluated sourceTail =>
     cases sourceEq : sources 0 with
     | cons head tailSource =>
       cases head with
       | byVal child =>
         have evidence := canonical 0
         rw [sourceEq] at evidence
         obtain ⟨found, childCanonical, _⟩ := evidence
         obtain ⟨point, frame, evaluated, executed, post, nextRows, nextRealized, nextBounded, nextChecked, nextInput⟩ :=
           accepted_generated_call_split_scalar_literal_stage source literal found child childCanonical admitted split input bounded realized checked extended
         obtain ⟨rfl, rfl⟩ := evalArg_success_unique sourceEvaluated evaluated
         have nextCells := cells.next found post
         have nextPost : Post cfg env cx before rootFrame
             (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2 frame point [] := by
           have combined := wholePost.comp post
           have takeEq : arguments.take (index + 1) = arguments.take index ++ [.byVal expression] := by
             rw [List.take_add_one, found]
             simp
           rw [takeEq, lowerArgs_append_run]
           simpa [lowerArgs, lowerArg, bind_run, pure_run] using combined.sub (by simp)
         let nextSources := ArgsSource.afterHead sources evaluated
         have nextCanonical : ∀ fuel, (nextSources fuel).CallChildren source (index + 1) := by
           intro fuel
           exact ArgsSource.afterHead_callChildren source sources canonical evaluated fuel
         obtain ⟨tailLength, finalPoint, finalFrame, finalValues, finalSlots, valuesEq, afterEq, done, tailSteps, finalAliases, finalRows,
           finalBounded, finalRealized, finalChecked, finalPost, finalCells, finalInput⟩ :=
           ih nextSources nextCanonical sourceTail nextRows nextPost nextCells nextInput nextBounded nextRealized nextChecked
         refine ⟨1 + tailLength, finalPoint, finalFrame, sourceValue :: finalValues, finalSlots,
           by simp [valuesEq], afterEq, .cons evaluated done, executed.append tailSteps, finalAliases, ?_, ?_, finalRealized, ?_, ?_, ?_, ?_⟩
         · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalRows
         · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalBounded
         · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalChecked
         · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPost
         · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.append_assoc] using finalCells
         · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalInput
  | @reference borrow slot mutability element rest type tail ih =>
    cases sourceDone with
    | @cons argument sourceRest sourceState middle sourceEnd sourceValue sourceVals sourceFuel sourceEvaluated sourceTail =>
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
         obtain ⟨rfl, rfl⟩ := evalArg_success_unique sourceEvaluated evaluated
         have nextCells := cells.next found post
         have nextPost : Post cfg env cx before rootFrame
             (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2 frame point [] := by
           have combined := wholePost.comp post
           have takeEq : arguments.take (index + 1) = arguments.take index ++ [.byRef borrow (.var slot)] := by
             rw [List.take_add_one, found]
             simp
           rw [takeEq, lowerArgs_append_run]
           simpa [lowerArgs, bind_run, pure_run] using combined.sub (by simp)
         let nextSources := ArgsSource.afterHead sources evaluated
         have nextCanonical : ∀ fuel, (nextSources fuel).CallChildren source (index + 1) := by
           intro fuel
           exact ArgsSource.afterHead_callChildren source sources canonical evaluated fuel
         obtain ⟨tailLength, finalPoint, finalFrame, finalValues, finalSlots, valuesEq, afterEq, done, tailSteps, finalAliases, finalRows,
           finalBounded, finalRealized, finalChecked, finalPost, finalCells, finalInput⟩ :=
           ih nextSources nextCanonical sourceTail nextRows nextPost nextCells nextInput nextBounded nextRealized nextChecked
         refine ⟨length + tailLength, finalPoint, finalFrame, .ref location :: finalValues, finalSlots,
           by simp [valuesEq], afterEq, .cons evaluated done, executed.append tailSteps, finalAliases, ?_, ?_, finalRealized, ?_, ?_, ?_, ?_⟩
         · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalRows
         · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalBounded
         · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalChecked
         · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPost
         · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.append_assoc] using finalCells
         · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalInput

#print axioms accepted_generated_call_split_mixed_forward
end Goose.Lower

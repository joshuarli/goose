import Goose.Lower.DemandCallReadsStop
import Goose.Lower.DemandCallSplitBooleanStage
import Goose.Lower.DemandCallSliceSequenceStage
import Goose.Lower.DemandRuntimePrefixSplit

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

inductive SplitMixedArguments (access : AccessEnv) : List Arg → Prop
  | nil : SplitMixedArguments access []
  | read {place : Place} {rest : List Arg} (form : ScalarReadPlace place) (tail : SplitMixedArguments access rest) :
      SplitMixedArguments access (.byVal (.read place) :: rest)
  | literal {expression : Expr} {value : Val} {operation : Op} {rest : List Arg}
      (form : CallScalarLiteral expression value operation) (tail : SplitMixedArguments access rest) :
      SplitMixedArguments access (.byVal expression :: rest)
  | reference {borrow : Mutability} {slot : VarId} {mutability : Mutability} {element : Ty} {rest : List Arg}
      (type : access.placeType? (.var slot) = some (.slice mutability element)) (tail : SplitMixedArguments access rest) :
      SplitMixedArguments access (.byRef borrow (.var slot) :: rest)

inductive CallSplitStoppedCells {cfg : Cfg} {env : Env} {initialState : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    (cx : FnCtx) (results : List Ty) (before : LS) (loop : Option LoopCtx) (map : RetainedSsaMap) (callFrame : GIR.Frame)
    (previousValues : List Val) (index : Nat) (rest : List Arg) (start : DemandRuntimePoint) (taken : Nat)
    (reached : DemandRuntimePoint) (stop : Stop) (after : St) : Prop
  | aborted (trace : CallArgumentsStopped cfg env rest start.state stop after) :
      CallSplitStoppedCells source cx results before loop map callFrame previousValues index rest start taken reached stop after
  | complete {consumed remaining : Nat} {boundary : DemandRuntimePoint} {values : List Val}
      {prior : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell}
      (count : consumed + remaining = taken)
      (executed : DemandRuntimePrefix cx consumed start boundary)
      (residual : DemandRuntimePrefix cx remaining boundary reached)
      (trace : CallArgumentsDone cfg env rest start.state values boundary.state)
      (tracked : SplitCallArgumentRows source.rootsEnv.access source.path 0
        (arguments.take (index + rest.length))
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).1 prior slots)
      (bounded : (⟨⟨prior ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Bounded
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
      (realized : (⟨⟨prior ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Realizes cfg.mod source.world env boundary)
      (checked : ∀ cell ∈ slots, cell.Checked source (index + rest.length) boundary.frame)
      (wholePost : Post cfg env cx before callFrame
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).2
        boundary.frame boundary.point [])
      (cells : CallArgumentCells
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).1
        (previousValues ++ values)
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).2.vals.size boundary.frame)
      (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
        (lowerArgs (arguments.take (index + rest.length)) (lowerEnv cfg.mod env.vars results) before).2 boundary.frame boundary.point) :
      CallSplitStoppedCells source cx results before loop map callFrame previousValues index rest start taken reached stop after

theorem accepted_generated_call_split_mixed_stop {cfg : Cfg} {env : Env} {initialState state : St}
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
    (readAdmitted : map.Admitted cfg.mod.profile source.context.retained)
    (coverage : map.Covers required)
    (shrink : cfg.mod.profile = .shrink)
    (split : SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 values slots)
    {initial callFrame : GIR.Frame} {start : Pt} {previousValues : List Val}
    (wholePost : Post cfg env cx before callFrame
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
    {taken : Nat} {runtime : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ runtime)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel runtime stop after) (nonTimeout : stop ≠ .timeout) :
    CallSplitStoppedCells source cx results before loop map callFrame previousValues index rest
      ⟨start, initial, state⟩ taken runtime stop after := by
  induction form generalizing index initial start values slots previousValues taken runtime with
  | nil =>
    apply CallSplitStoppedCells.complete (consumed := 0) (remaining := taken) (boundary := ⟨start, initial, state⟩)
      (values := []) (prior := values) (slots := slots) (by omega) (.zero _) steps (.nil state)
    · simpa using split
    · simpa using bounded
    · exact realized
    · simpa using checked
    · simpa using wholePost
    · simpa using cells
    · simpa using input
  | @read place rest readForm tail ih =>
    cases sourceEq : sources 0 with
    | cons head tailSource =>
      cases head with
      | byVal child =>
        have evidence := canonical 0
        rw [sourceEq] at evidence
        obtain ⟨found, childCanonical, _⟩ := evidence
        by_cases early : taken < 2
        · exact .aborted (.head (accepted_generated_call_split_read_stop source found child readForm childCanonical
            occurrence rows coverage split realized input extended early steps stopped nonTimeout) nonTimeout)
        · have enough : 2 ≤ taken := by omega
          obtain ⟨middle, aliases, value, leading, residual, evaluated, sameState, post, nextRows,
            nextRealized, nextBounded, nextChecked, nextInput⟩ :=
            accepted_generated_call_split_read_prefix_post source found child readForm childCanonical occurrence rows coverage split
              realized readAdmitted bounded input extended shrink checked enough steps
          cases middle with
          | mk point frame nextState =>
            simp only at sameState
            subst nextState
            have nextCells := cells.next found post
            have nextPost : Post cfg env cx before callFrame
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
            have next := ih nextSources nextCanonical nextRows nextPost nextCells nextInput nextBounded nextRealized nextChecked residual stopped
            cases next with
            | aborted trace => exact .aborted (.tail evaluated trace)
            | @complete consumed remaining final vals finalPrior finalSlots count executed suffix trace finalRows finalBounded finalRealized finalChecked finalPost finalCells finalInput =>
              apply CallSplitStoppedCells.complete (consumed := 2 + consumed) (remaining := remaining)
                (boundary := final) (values := value :: vals) (prior := finalPrior) (slots := finalSlots) (by omega)
                (leading.append executed) suffix (.cons evaluated trace)
              · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalRows
              · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalBounded
              · exact finalRealized
              · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalChecked
              · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPost
              · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.append_assoc] using finalCells
              · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalInput

  | @literal expression value operation rest literal tail ih =>
    cases sourceEq : sources 0 with
    | cons head tailSource =>
      cases head with
      | byVal child =>
        have evidence := canonical 0
        rw [sourceEq] at evidence
        obtain ⟨found, childCanonical, _⟩ := evidence
        obtain ⟨point, frame, evaluated, executed, post, nextRows, nextRealized, nextBounded, nextChecked, nextInput⟩ :=
          accepted_generated_call_split_scalar_literal_stage source literal found child childCanonical readAdmitted split input bounded realized checked extended
        have bound := executed.length_le_stopped steps stopped nonTimeout
        obtain ⟨remaining, count, residual⟩ := executed.split_at bound steps
        have nextCells := cells.next found post
        have nextPost : Post cfg env cx before callFrame
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
        have next := ih nextSources nextCanonical nextRows nextPost nextCells nextInput nextBounded nextRealized nextChecked residual stopped
        cases next with
        | aborted trace => exact .aborted (.tail evaluated trace)
        | @complete consumed remainingTail final vals finalPrior finalSlots tailCount tailExecuted suffix trace finalRows finalBounded finalRealized finalChecked finalPost finalCells finalInput =>
          apply CallSplitStoppedCells.complete (consumed := 1 + consumed) (remaining := remainingTail)
            (boundary := final) (values := value :: vals) (prior := finalPrior) (slots := finalSlots) (by omega)
            (executed.append tailExecuted) suffix (.cons evaluated trace)
          · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalRows
          · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalBounded
          · exact finalRealized
          · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalChecked
          · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPost
          · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.append_assoc] using finalCells
          · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalInput
  | @reference borrow slot mutability element rest type tail ih =>
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
        have bound := executed.length_le_stopped steps stopped nonTimeout
        obtain ⟨remaining, count, residual⟩ := executed.split_at bound steps
        have nextCells := cells.next found post
        have nextPost : Post cfg env cx before callFrame
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
        have next := ih nextSources nextCanonical nextRows nextPost nextCells nextInput nextBounded nextRealized nextChecked residual stopped
        cases next with
        | aborted trace => exact .aborted (.tail evaluated trace)
        | @complete consumed remainingTail final vals finalPrior finalSlots tailCount tailExecuted suffix trace finalRows finalBounded finalRealized finalChecked finalPost finalCells finalInput =>
          apply CallSplitStoppedCells.complete (consumed := length + consumed) (remaining := remainingTail)
            (boundary := final) (values := .ref location :: vals) (prior := finalPrior) (slots := finalSlots) (by omega)
            (executed.append tailExecuted) suffix (.cons evaluated trace)
          · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalRows
          · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalBounded
          · exact finalRealized
          · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalChecked
          · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPost
          · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.append_assoc] using finalCells
          · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalInput

#print axioms accepted_generated_call_split_mixed_stop

end Goose.Lower

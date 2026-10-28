import Goose.Lower.DemandCallSplitCoverage

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_generated_call_slice_sequence_stage {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {borrow : Mutability} {slot : VarId}
    (found : arguments[index]? = some (.byRef borrow (.var slot)))
    (child : PlaceSource cfg env (.var slot) state)
    (target : child.ty.refTarget = true ∨ (child.ty.isSlice = true ∧ child.mutable = true ∧ (Place.var slot).sliceArg = true))
    (canonical : (ArgSource.byRef borrow child target).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byRef borrow (.var slot)) found))
    {mutability : Mutability} {element : Ty} (type : child.ty = .slice mutability element)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
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
    ∃ (location : Loc) (length : Nat) (point : Pt) (frame : GIR.Frame) (cell : SliceSlotArgumentCell),
      let stage := (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2
      let id := (lowerArg (.byRef borrow (.var slot)) (lowerEnv cfg.mod env.vars results) stage).1
      evalArg 2 cfg env (.byRef borrow (.var slot)) state = .ok (.ref location) state ∧
      DemandRuntimePrefix cx length ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      Post cfg env cx stage initial (lowerArg (.byRef borrow (.var slot)) (lowerEnv cfg.mod env.vars results) stage).2
        frame point [(id, .val (.ref location))] ∧
      SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take (index + 1))
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).1 values (slots ++ [cell]) ∧
      (⟨⟨values ++ map.values, map.runs⟩, slots ++ [cell]⟩ : SplitCallRetained).Bounded
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      (⟨⟨values ++ map.values, map.runs⟩, slots ++ [cell]⟩ : SplitCallRetained).Realizes
        cfg.mod source.world env ⟨point, frame, state⟩ ∧
      (∀ next ∈ slots ++ [cell], next.Checked source (index + 1) frame) ∧
      GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2 frame point := by
  obtain ⟨prior, tracked, _, _, _⟩ := split.generatedRows
  obtain ⟨location, length, point, frame, cell, evaluated, executed, post, cellValue, cellIndex, cellChecked, cellAlias, nextRows⟩ :=
    accepted_generated_call_slice_argument_rows source found child target canonical type occurrence rows tracked split input.atPoint input.related extended
  have kept := realized.1.retained post.same bounded.1.1 bounded.1.2 RetainsAliases.refl
  have nextBounded : (⟨⟨values ++ map.values, map.runs⟩, slots ++ [cell]⟩ : SplitCallRetained).Bounded
      (lowerArg (.byRef borrow (.var slot)) (lowerEnv cfg.mod env.vars results)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).2.vals.size := by
    constructor
    · exact bounded.1.mono post.mono
    · intro next member
      rcases List.mem_append.mp member with old | fresh
      · exact Nat.lt_of_lt_of_le (bounded.2 next old) post.mono
      · simp only [List.mem_singleton] at fresh
        subst next
        rw [cellValue]
        exact post.lt (_, .val (.ref location)) (by simp)
  have nextRealized : (⟨⟨values ++ map.values, map.runs⟩, slots ++ [cell]⟩ : SplitCallRetained).Realizes
      cfg.mod source.world env ⟨point, frame, state⟩ := by
    constructor
    · exact kept
    · intro next member
      rcases List.mem_append.mp member with old | fresh
      · exact (realized.2 next old).transport (post.same next.value (bounded.2 next old)) (by intros; rfl) RetainsAlias.refl
      · simp only [List.mem_singleton] at fresh
        subst next
        have checkedType := cellChecked
        obtain ⟨_, _, _, _, _, _, _, aliasType, _, _⟩ := checkedType
        have outputType := cellAlias
        obtain ⟨_, _, _, _, _, _, _, _, actualType, _⟩ := outputType
        have types : cell.mutability = mutability ∧ cell.element = element := Ty.slice.inj (aliasType.symm.trans actualType)
        simpa only [cellValue, types.1, types.2] using cellAlias
  have nextChecked : ∀ next ∈ slots ++ [cell], next.Checked source (index + 1) frame := by
    intro next member
    rcases List.mem_append.mp member with old | fresh
    · exact SliceSlotArgumentCell.advance (checked next old) (by omega) post (bounded.2 next old)
    · simp only [List.mem_singleton] at fresh
      subst next
      exact cellChecked
  let le := lowerEnv cfg.mod env.vars results
  let stage := (lowerArgs (arguments.take index) le before).2
  have advance := advB_lowerArg (.byRef borrow (.var slot)) le stage _ _ rfl
  have nextInput : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArg (.byRef borrow (.var slot)) le stage).2 frame point :=
    ⟨input.metadata, input.loops, post.pp, post.rel, input.moduleEq, input.resultsEq,
      input.depth, (by cases loop <;> exact input.targets), input.counter.afterPost (post.sub (by simp)),
      input.generated.lowerArg (.byRef borrow (.var slot)) rfl, input.frames.mono advance.ext⟩
  have takeEq : arguments.take (index + 1) = arguments.take index ++ [.byRef borrow (.var slot)] := by
    rw [List.take_add_one, found]
    simp
  have nextInput' : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take (index + 1)) le before).2 frame point := by
    rw [takeEq, lowerArgs_append_run]
    simpa [lowerArgs, bind_run, pure_run, stage] using nextInput
  have nextBounded' : (⟨⟨values ++ map.values, map.runs⟩, slots ++ [cell]⟩ : SplitCallRetained).Bounded
      (lowerArgs (arguments.take (index + 1)) le before).2.vals.size := by
    rw [takeEq, lowerArgs_append_run]
    simpa [lowerArgs, bind_run, pure_run, stage] using nextBounded
  exact ⟨location, length, point, frame, cell, evaluated, executed, post, nextRows, nextBounded', nextRealized, nextChecked, nextInput'⟩

#print axioms accepted_generated_call_slice_sequence_stage
end Goose.Lower

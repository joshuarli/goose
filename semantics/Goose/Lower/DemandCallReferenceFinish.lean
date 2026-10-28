import Goose.Lower.DemandCallReferenceBorrow

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_call_reference_finish {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {mutability : Mutability} {place : Place}
    (found : arguments[index]? = some (.byRef mutability place)) (child : PlaceSource cfg env place state)
    (target : child.ty.refTarget = true)
    (canonical : (ArgSource.byRef mutability child (Or.inl target)).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byRef mutability place) found))
    (form : ScalarReadPlace place) {location : Loc}
    (placed : evalPlace 1 cfg env place state = .ok location state)
    {cx : FnCtx} {results : List Ty} {before : LS} {loop : Option LoopCtx}
    {prior : List (ValueId × RetainedAlias)} {map : RetainedSsaMap}
    (tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 prior)
    {initial frame : GIR.Frame} {start point : Pt}
    (bounded : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    (post : Post cfg env cx (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial
      (lowerArg (.byRef mutability place) (lowerEnv cfg.mod env.vars results)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).2 frame point
      [((lowerArg (.byRef mutability place) (lowerEnv cfg.mod env.vars results)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1, .val (.ref location))]) :
    ∃ aliases : List RetainedAlias, let id := (lowerArg (.byRef mutability place) (lowerEnv cfg.mod env.vars results)
          (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1
      let nextPrior := prior ++ aliases.map (fun alias => (id, alias))
      GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take (index + 1))
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).1 nextPrior ∧
      (⟨nextPrior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env ⟨point, frame, state⟩ ∧
      (⟨nextPrior ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2 frame point := by
  let le := lowerEnv cfg.mod env.vars results
  let stage := (lowerArgs (arguments.take index) le before).2
  let id := (lowerArg (.byRef mutability place) le stage).1
  have bound : index < arguments.length := (List.getElem?_eq_some_iff.mp found).1
  have takeEq : arguments.take (index + 1) = arguments.take index ++ [.byRef mutability place] := by
    rw [List.take_add_one, found]
    simp
  have argsEq : lowerArgs (arguments.take (index + 1)) le before =
      ((lowerArgs (arguments.take index) le before).1 ++ [id], (lowerArg (.byRef mutability place) le stage).2) := by
    rw [takeEq, lowerArgs_append_run]
    simp [lowerArgs, bind_run, pure_run, stage, id]
  have preserved := realized.retained post.same bounded.1 bounded.2 RetainsAliases.refl
  obtain ⟨aliases, query, realizedNext⟩ := accepted_call_reference_retained source found child target canonical form placed post preserved
  let fresh := aliases.map (fun alias => (id, alias))
  have nextTracked := tracked.snoc (argument := .byRef mutability place) (id := id)
    (by simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)] using query)
  have nextRealized : (⟨(prior ++ fresh) ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env ⟨point, frame, state⟩ := by
    constructor
    · intro cell member
      apply realizedNext.1 cell
      simp only [RetainedSsaMap.addValues, RetainedSsaMap.values, List.mem_append] at member ⊢
      rcases member with (old | added) | old
      · exact Or.inr (Or.inl old)
      · exact Or.inl added
      · exact Or.inr (Or.inr old)
    · exact realizedNext.2
  have idBound : id < (lowerArg (.byRef mutability place) le stage).2.vals.size := post.lt (id, .val (.ref location)) (by simp [id, le, stage])
  have nextBounded : (⟨(prior ++ fresh) ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
      (lowerArg (.byRef mutability place) le stage).2.vals.size := by
    constructor
    · intro cell member
      simp only [List.mem_append] at member
      rcases member with (old | added) | old
      · exact Nat.lt_of_lt_of_le (bounded.1 cell (List.mem_append_left _ old)) post.mono
      · obtain ⟨alias, _, rfl⟩ := List.mem_map.mp added
        exact idBound
      · exact Nat.lt_of_lt_of_le (bounded.1 cell (List.mem_append_right _ old)) post.mono
    · intro cell member
      exact Nat.lt_of_lt_of_le (bounded.2 cell member) post.mono
  have advance := advB_lowerArg (.byRef mutability place) le stage _ _ rfl
  have nextInput : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArg (.byRef mutability place) le stage).2 frame point :=
    ⟨input.metadata, input.loops, post.pp, post.rel, input.moduleEq, input.resultsEq,
      input.depth, (by cases loop <;> exact input.targets), input.counter.afterPost (post.sub (by simp)),
      input.generated.lowerArg (.byRef mutability place) rfl, input.frames.mono advance.ext⟩
  refine ⟨aliases, ?_, nextRealized, ?_, ?_⟩
  · rw [argsEq, takeEq]
    simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound), id, fresh] using nextTracked
  · rw [argsEq]
    exact nextBounded
  · rw [argsEq]
    exact nextInput

#print axioms accepted_call_reference_finish
end Goose.Lower

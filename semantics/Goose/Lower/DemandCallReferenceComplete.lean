import Goose.Lower.DemandCallReferenceFinish
import Goose.Lower.DemandCallReferenceBorrowDemand
import Goose.Lower.DemandCallReferenceDemand

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_generated_call_reference_complete_demand {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {mutability : Mutability} {place : Place}
    (found : arguments[index]? = some (.byRef mutability place)) (child : PlaceSource cfg env place state)
    (target : child.ty.refTarget = true)
    (canonical : (ArgSource.byRef mutability child (Or.inl target)).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byRef mutability place) found))
    (form : ScalarReadPlace place) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {prior : List (ValueId × RetainedAlias)}
    (tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 prior)
    {initial : GIR.Frame} {start : Pt}
    (bounded : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (location : Loc) (length : Nat) (point : Pt) (frame : GIR.Frame) (aliases : List RetainedAlias),
      let stage := (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2
      let address := (lowerPlace place (lowerEnv cfg.mod env.vars results) stage).1
      let middle : DemandRuntimePoint := ⟨(start.1, start.2 + 1), initial.set address (.val (.ref location)), state⟩
      let id := (lowerArg (.byRef mutability place) (lowerEnv cfg.mod env.vars results) stage).1
      let nextPrior := prior ++ aliases.map (fun alias => (id, alias))
      evalArg 2 cfg env (.byRef mutability place) state = .ok (.ref location) state ∧
      DemandUniformTraversal cx
        (fun runtime => (DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.inputFuture
            (prior ++ map.values) map.runs runtime ∨
          DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
            (prior ++ map.values) map.runs runtime) ∧ Same stage.vals.size initial runtime.frame)
        (length + 1) ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      (∀ fuel, DemandInstructionStep cx fuel ⟨start, initial, state⟩ middle) ∧
      DemandRuntimePrefix cx length middle ⟨point, frame, state⟩ ∧
      Post cfg env cx stage initial (lowerArg (.byRef mutability place) (lowerEnv cfg.mod env.vars results) stage).2
        frame point [(id, .val (.ref location))] ∧
      GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take (index + 1))
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).1 nextPrior ∧
      (⟨nextPrior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env ⟨point, frame, state⟩ ∧
      (⟨nextPrior ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2 frame point := by
  let le := lowerEnv cfg.mod env.vars results
  let stage := (lowerArgs (arguments.take index) le before).2
  let address := (lowerPlace place le stage).1
  let middle := (lowerPlace place le stage).2
  obtain ⟨location, placed, addressPost, firstStep⟩ :=
    accepted_generated_call_reference_address source found child (Or.inl target) canonical form occurrence rows tracked input.atPoint input.related extended
  have argExtended := generated_call_argument_extended found extended
  have argEq : lowerArg (.byRef mutability place) le stage = borrowTo mutability address le middle := by
    simp [lowerArg, bind_run, address, middle]
  have borrowExtended : ExtT (borrowTo mutability address le middle).2 cx.fn.blocks := by
    rw [← argEq]
    exact argExtended
  obtain ⟨addressLocation, addressPlaced, placeEntry, placeAddressed, _⟩ :=
    accepted_generated_call_reference_demand source found child (Or.inl target) canonical form occurrence rows tracked
      input.atPoint input.related bounded realized extended
  have sameLocation : addressLocation = location := by
    have same := addressPlaced.symm.trans placed
    exact (Res.ok.inj same).1
  subst addressLocation
  have childRealized : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod child.world env ⟨start, initial, state⟩ := by
    obtain ⟨_, _, world, _, _, _⟩ := canonical
    simpa only [RetainedSsaMap.Realizes, world] using realized
  have sourceFrame := (child.result 1 location placed).frame
  obtain ⟨borrowLength, finalPoint, finalFrame, borrowTraversal, borrowPost⟩ :=
    generated_call_reference_borrow_demand addressPost mutability le borrowExtended sourceFrame bounded childRealized
  have borrowSteps : DemandRuntimePrefix cx borrowLength
      ⟨(start.1, start.2 + 1), initial.set address (.val (.ref location)), state⟩ ⟨finalPoint, finalFrame, state⟩ := by
    have forget {length : Nat} {first last : DemandRuntimePoint}
        (path : DemandUniformTraversal cx
          (fun runtime => DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
            (prior ++ map.values) map.runs runtime ∧ Same stage.vals.size initial runtime.frame) length first last) : DemandRuntimePrefix cx length first last := by
      induction path with
      | done _ => exact .zero _
      | next _ step tail ih => exact .next ((step 0).runtime) ih
    exact forget borrowTraversal
  have totalTraversal : DemandUniformTraversal cx
      (fun runtime => (DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.inputFuture
          (prior ++ map.values) map.runs runtime ∨
        DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
          (prior ++ map.values) map.runs runtime) ∧ Same stage.vals.size initial runtime.frame)
      (borrowLength + 1) ⟨start, initial, state⟩ ⟨finalPoint, finalFrame, state⟩ :=
    .next ⟨.inl placeEntry, Same.refl _ _⟩ firstStep (borrowTraversal.mono (fun _ valid => ⟨.inr valid.1, valid.2⟩))
  have finalPost : Post cfg env cx stage initial (lowerArg (.byRef mutability place) le stage).2 finalFrame finalPoint
      [((lowerArg (.byRef mutability place) le stage).1, .val (.ref location))] := by
    rw [argEq]
    exact borrowPost
  obtain ⟨aliases, nextTracked, nextRealized, nextBounded, nextInput⟩ :=
    accepted_call_reference_finish source found child target canonical form placed tracked bounded realized input finalPost
  refine ⟨location, borrowLength, finalPoint, finalFrame, aliases, ?_, totalTraversal, firstStep, borrowSteps, finalPost, nextTracked, nextRealized, nextBounded, nextInput⟩
  simpa [evalArg, bind_apply, placed, pure_apply]


theorem accepted_generated_call_reference_complete {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {mutability : Mutability} {place : Place}
    (found : arguments[index]? = some (.byRef mutability place)) (child : PlaceSource cfg env place state)
    (target : child.ty.refTarget = true)
    (canonical : (ArgSource.byRef mutability child (Or.inl target)).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byRef mutability place) found))
    (form : ScalarReadPlace place) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {prior : List (ValueId × RetainedAlias)}
    (tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 prior)
    {initial : GIR.Frame} {start : Pt}
    (bounded : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (location : Loc) (length : Nat) (point : Pt) (frame : GIR.Frame) (aliases : List RetainedAlias),
      let stage := (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2
      let address := (lowerPlace place (lowerEnv cfg.mod env.vars results) stage).1
      let middle : DemandRuntimePoint := ⟨(start.1, start.2 + 1), initial.set address (.val (.ref location)), state⟩
      let id := (lowerArg (.byRef mutability place) (lowerEnv cfg.mod env.vars results) stage).1
      let nextPrior := prior ++ aliases.map (fun alias => (id, alias))
      evalArg 2 cfg env (.byRef mutability place) state = .ok (.ref location) state ∧
      (∀ fuel, DemandInstructionStep cx fuel ⟨start, initial, state⟩ middle) ∧
      DemandRuntimePrefix cx length middle ⟨point, frame, state⟩ ∧
      Post cfg env cx stage initial (lowerArg (.byRef mutability place) (lowerEnv cfg.mod env.vars results) stage).2
        frame point [(id, .val (.ref location))] ∧
      GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take (index + 1))
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).1 nextPrior ∧
      (⟨nextPrior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env ⟨point, frame, state⟩ ∧
      (⟨nextPrior ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2 frame point := by
  obtain ⟨location, length, point, frame, aliases, evaluated, _, first, tail, post, tracked, realized, bounded, input⟩ :=
    accepted_generated_call_reference_complete_demand source found child target canonical form occurrence rows tracked bounded realized input extended
  exact ⟨location, length, point, frame, aliases, evaluated, first, tail, post, tracked, realized, bounded, input⟩

#print axioms accepted_generated_call_reference_complete_demand
#print axioms accepted_generated_call_reference_complete
end Goose.Lower

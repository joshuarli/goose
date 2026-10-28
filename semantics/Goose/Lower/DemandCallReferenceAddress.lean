import Goose.Lower.DemandCallValueStage

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem generated_call_argument_extended {cfg : Cfg} {env : Env} {context : ContextId}
    {arguments : List Arg} {origin : OriginId} {index : Nat} {argument : Arg}
    (found : arguments[index]? = some argument) {cx : FnCtx} {results : List Ty} {before : LS}
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ExtT (lowerArg argument (lowerEnv cfg.mod env.vars results)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).2 cx.fn.blocks := by
  let le := lowerEnv cfg.mod env.vars results
  let stage := (lowerArgs (arguments.take index) le before).2
  obtain ⟨ids, middle, after, argsRun, definition, tail⟩ := lowerExpr_call_split
    (show lowerExpr (.call context arguments origin) le before =
      ((lowerExpr (.call context arguments origin) le before).1, (lowerExpr (.call context arguments origin) le before).2) from rfl)
  have afterExtended : ExtT after cx.fn.blocks := by
    rcases tail with ⟨_, term⟩ | ⟨_, rfl⟩
    · exact extended.of_adv (adv_emitTerm term)
    · exact extended
  have middleExtended := afterExtended.of_adv (adv_emitDef definition)
  have argsExtended : ExtT (lowerArgs arguments le before).2 cx.fn.blocks := by
    rw [argsRun]
    exact middleExtended
  obtain ⟨earlier, later, split, length, _, _, advance⟩ := lowerArgs_argument_checkpoint found le before
  have earlierEq : arguments.take index = earlier := by
    rw [split, ← length]
    simp
  have argExtended : ExtT (lowerArg argument le stage).2 cx.fn.blocks := by
    dsimp [stage]
    rw [earlierEq]
    exact argsExtended.of_adv advance
  exact argExtended

theorem accepted_generated_call_reference_address {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {mutability : Mutability} {place : Place}
    (found : arguments[index]? = some (.byRef mutability place)) (child : PlaceSource cfg env place state)
    (target : child.ty.refTarget = true ∨ (child.ty.isSlice = true ∧ child.mutable = true ∧ place.sliceArg = true))
    (canonical : (ArgSource.byRef mutability child target).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byRef mutability place) found))
    (form : ScalarReadPlace place) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {prior : List (ValueId × RetainedAlias)}
    (tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 prior)
    {frame : GIR.Frame} {point : Pt}
    (atPoint : (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.pp = some point)
    (related : Rel cfg env cx frame (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ location : Loc,
      evalPlace 1 cfg env place state = .ok location state ∧
      Post cfg env cx (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 frame
        (lowerPlace place (lowerEnv cfg.mod env.vars results)
          (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).2
        (frame.set (lowerPlace place (lowerEnv cfg.mod env.vars results)
          (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1 (.val (.ref location)))
        (point.1, point.2 + 1) [((lowerPlace place (lowerEnv cfg.mod env.vars results)
          (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1, .val (.ref location))] ∧
      ∀ fuel, DemandInstructionStep cx fuel ⟨point, frame, state⟩
        ⟨(point.1, point.2 + 1), frame.set (lowerPlace place (lowerEnv cfg.mod env.vars results)
          (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1 (.val (.ref location)), state⟩ := by
  obtain ⟨plans, path, world, typing, roots, childContext⟩ := canonical
  have argumentOccurrence := GeneratedDemandOccurrence.argument occurrence found
  have argumentRows := GeneratedDemandRows.argument rows (argumentAt := found) tracked
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root child.path (.place place) (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 := by
    rw [path]
    exact .argumentPlace argumentOccurrence
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence ⟨prior ++ required.values, required.runs⟩ := by
    have inherited := GeneratedDemandRows.argumentPlace argumentRows
    simpa only [roots, path] using inherited
  let le := lowerEnv cfg.mod env.vars results
  let stage := (lowerArgs (arguments.take index) le before).2
  have argExtended := generated_call_argument_extended found extended
  have argEq : (lowerArg (.byRef mutability place) le stage).2 =
      (borrowTo mutability (lowerPlace place le stage).1 le (lowerPlace place le stage).2).2 := by
    simp [lowerArg, bind_run]
  rw [argEq] at argExtended
  have placeExtended : ExtT (lowerPlace place le stage).2 cx.fn.blocks :=
    argExtended.of_adv (advB_borrowTo mutability (lowerPlace place le stage).1 le (lowerPlace place le stage).2 _ _ rfl)
  exact accepted_generated_scalar_place_address child form childOccurrence childRows atPoint related placeExtended

#print axioms accepted_generated_call_reference_address
end Goose.Lower

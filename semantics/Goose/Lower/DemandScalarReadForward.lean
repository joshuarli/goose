import Goose.Lower.DemandScalarReadCursor
import Goose.Lower.DemandRunAtPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_scalar_read_forward {cfg : Cfg} {env : Env} {place : Place} {state after : St} {value : Val}
    (source : ExprSource cfg env (.read place) state) (form : ScalarReadPlace place)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.read place)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {initial : GIR.Frame} {start : Pt} (point : before.pp = some start) (related : Rel cfg env cx initial before)
    (extended : ExtT (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (evaluated : evalExpr 2 cfg env (.read place) state = .ok value after) :
    after = state ∧ ∃ (finish : DemandRuntimePoint),
      DemandRuntimePrefix cx 2 ⟨start, initial, state⟩ finish ∧ finish.state = state ∧
      Post cfg env cx before initial (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results) before).2
        finish.frame finish.point [((lowerExpr (.read place) (lowerEnv cfg.mod env.vars results) before).1, .val value)] := by
  let le := lowerEnv cfg.mod env.vars results
  let addressed := lowerPlace place le before
  let loaded := emitDef (.load addressed.1) le addressed.2
  let built := lowerExpr (.read place) le before
  obtain ⟨child, typing, roots, metadata⟩ := source.readChild
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.place place) before := by
    rw [metadata.path]
    exact .first occurrence (.expressionPlace rfl)
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited := GeneratedDemandRows.first (first := .expressionPlace rfl) rows
    simpa only [roots, metadata.path] using inherited
  obtain ⟨location, placed, post, firstStep⟩ := accepted_generated_scalar_place_address child form
    childOccurrence childRows point related (generated_read_place_extended extended)
  have read : readLoc location state = .ok value after := by
    simpa only [evalExpr, bind_apply, placed] using evaluated
  have same : after = state := by
    unfold readLoc at read
    cases result : state.store.read location <;> simp [result] at read
    exact read.2.symm
  subst after
  let middleFrame := initial.set addressed.1 (.val (.ref location))
  have addressCell : middleFrame.vals[addressed.1]? = some (.val (.ref location)) := by
    simpa only [middleFrame, addressed, le] using post.has (addressed.1, .val (.ref location)) (by simp [addressed, le])
  have loadEmit : emitDef (.load addressed.1) le addressed.2 = (loaded.1, loaded.2) := rfl
  obtain ⟨loadPost, instruction⟩ := Post.def_leaf post loadEmit (generated_read_load_extended extended) (.val value)
  have loadStep : DemandInstructionStep cx 0 ⟨(start.1, start.2 + 1), middleFrame, state⟩
      ⟨(start.1, start.2 + 2), middleFrame.set loaded.1 (.val value), state⟩ := by
    apply DemandInstructionStep.definition instruction
    simp [execOp, execPure, getVal_of addressCell, expectRef, bind_apply, pure_apply, Functor.map, M.bind', M.pure', read]
  have recordRun : recordReadValueRootRecipe loaded.1 place le loaded.2 =
      ((), (recordReadValueRootRecipe loaded.1 place le loaded.2).2) := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  have finalPost : Post cfg env cx before initial built.2 (middleFrame.set loaded.1 (.val value))
      (start.1, start.2 + 2) [(built.1, .val value)] := by
    simpa only [built, lowerExpr_read_run, Nat.add_assoc] using Post.recordReadValueRootRecipe loadPost recordRun
  refine ⟨rfl, ⟨(start.1, start.2 + 2), middleFrame.set loaded.1 (.val value), state⟩, ?_, rfl, finalPost⟩
  exact .next (firstStep 0).runtime (.next loadStep.runtime (.zero _))

#print axioms accepted_generated_scalar_read_forward
end Goose.Lower

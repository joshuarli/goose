import Goose.Lower.DemandScalarReadForward

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_scalar_read_stop_forward {cfg : Cfg} {env : Env} {place : Place} {state after : St} {stop : Stop}
    (source : ExprSource cfg env (.read place) state) (form : ScalarReadPlace place)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.read place)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {initial : GIR.Frame} {start : Pt} (point : before.pp = some start) (related : Rel cfg env cx initial before)
    (extended : ExtT (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (evaluated : evalExpr 2 cfg env (.read place) state = .stop stop after) :
    ∃ middle, DemandRuntimePrefix cx 1 ⟨start, initial, state⟩ middle ∧
      DemandInstructionStop cx 1 middle stop after := by
  let le := lowerEnv cfg.mod env.vars results
  let addressed := lowerPlace place le before
  obtain ⟨child, typing, roots, metadata⟩ := source.readChild
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.place place) before := by
    rw [metadata.path]
    exact .first occurrence (.expressionPlace rfl)
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited := GeneratedDemandRows.first (first := .expressionPlace rfl) rows
    simpa only [roots, metadata.path] using inherited
  obtain ⟨location, placed, post, firstStep⟩ := accepted_generated_scalar_place_address child form
    childOccurrence childRows point related (generated_read_place_extended extended)
  have read : readLoc location state = .stop stop after := by
    simpa only [evalExpr, bind_apply, placed] using evaluated
  let middleFrame := initial.set addressed.1 (.val (.ref location))
  have addressCell : middleFrame.vals[addressed.1]? = some (.val (.ref location)) := by
    simpa only [middleFrame, addressed, le] using post.has (addressed.1, .val (.ref location)) (by simp [addressed, le])
  have actualCell : middleFrame.vals[(lowerPlace place (lowerEnv cfg.mod env.vars results) before).1]? = some (.val (.ref location)) := by
    simpa [addressed, le] using addressCell
  have site := GeneratedDemandInstruction.load_auto occurrence rows post.pp extended
  refine ⟨⟨(start.1, start.2 + 1), middleFrame, state⟩, .next (firstStep 0).runtime (.zero _), ?_⟩
  apply DemandInstructionStop.definition site.instruction
  simp [execOp, execPure, getVal_of actualCell, expectRef, bind_apply, pure_apply, Functor.map, M.bind', M.pure', read]

#print axioms accepted_generated_scalar_read_stop_forward
end Goose.Lower

import Goose.Lower.DemandCallReferenceAlias

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem generated_call_reference_borrow {cfg : Cfg} {env : Env} {cx : FnCtx}
    {before middle : LS} {initial frame : GIR.Frame} {point : Pt} {state : St} {location : Loc} {id : ValueId}
    (post : Post cfg env cx before initial middle frame point [(id, .val (.ref location))])
    (mutability : Mutability) (le : LEnv)
    (extended : ExtT (borrowTo mutability id le middle).2 cx.fn.blocks) :
    ∃ length finalPoint finalFrame,
      DemandRuntimePrefix cx length ⟨point, frame, state⟩ ⟨finalPoint, finalFrame, state⟩ ∧
      Post cfg env cx before initial (borrowTo mutability id le middle).2 finalFrame finalPoint
        [((borrowTo mutability id le middle).1, .val (.ref location))] := by
  let result := borrowTo mutability id le middle
  have run : borrowTo mutability id le middle = (result.1, result.2) := rfl
  have cell := post.has (id, .val (.ref location)) (by simp)
  rcases borrowTo_ref_cases run with same | freeze | owner
  · obtain ⟨resultId, resultState⟩ := same
    refine ⟨0, point, frame, .zero _, ?_⟩
    change Post cfg env cx before initial result.2 frame point [(result.1, .val (.ref location))]
    rw [resultId, resultState]
    exact post
  · obtain ⟨final, instruction⟩ := Post.def_leaf post freeze extended (.val (.ref location))
    refine ⟨1, (point.1, point.2 + 1), frame.set result.1 (.val (.ref location)), ?_, final⟩
    exact .next (.define instruction (fuel := 0) (by simp [execOp, execPure, getVal_of cell, expectRef, pure_apply])) (.zero _)
  · obtain ⟨final, instruction⟩ := Post.def_leaf post owner extended (.val (.ref location))
    refine ⟨1, (point.1, point.2 + 1), frame.set result.1 (.val (.ref location)), ?_, final⟩
    exact .next (.define instruction (fuel := 0) (by simp [execOp, execPure, getVal_of cell, expectRef, pure_apply])) (.zero _)

#print axioms generated_call_reference_borrow
end Goose.Lower

import Goose.Lower.DemandIfCondition
import Goose.Lower.DemandBranchBlockStopped

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_if_branch_step {condition : ValueId} {le : LEnv} {before forked : LS}
    {yes no : BlockId} {point : Pt} {cx : FnCtx} {frame : GIR.Frame} {state : St} (value : Bool)
    (fork : fork condition le before = ((yes, no), forked))
    (atPoint : before.pp = some point) (extended : ExtT forked cx.fn.blocks)
    (cell : frame.vals[condition]? = some (.val (.bool value))) (fuel : Nat) :
    DemandInstructionStep cx fuel ⟨point, frame, state⟩ ⟨(if value then yes else no, 0), frame, state⟩ := by
  obtain ⟨_, _, _, _, _, _, instruction, yesAt, noAt⟩ := fork_facts fork atPoint extended
  obtain ⟨yesBlock, yesBlockAt, yesParameters⟩ := extended.params yesAt
  obtain ⟨noBlock, noBlockAt, noParameters⟩ := extended.params noAt
  let branch : DemandBranch := .conditional condition yes [] no []
  have branchAt : instAt cx.fn point = some (.term branch.term) := by
    simpa only [instAt_eq, branch, DemandBranch.term] using instruction
  have execution : branch.enter cx.fn frame state =
      .ok (if value then yes else no, instsAt cx.fn (if value then yes else no, 0), frame) state := by
    cases value <;>
      simp [branch, DemandBranch.enter, getVal, getCell, cell, Core.expectBool, mapList, enterBlock,
        yesBlockAt, noBlockAt, yesParameters, noParameters, bindParams, instsAt, bind_apply, pure_apply]
  exact .control branchAt execution

#print axioms generated_if_branch_step
end Goose.Lower

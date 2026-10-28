import Goose.Lower.DemandWhileTest

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_while_back_edge {le : LEnv} {header : BlockId} {before after : LS} {point : Pt}
    {cx : FnCtx} {frame : GIR.Frame} {state : St}
    (lowered : emitTerm (.br header []) le before = ((), after))
    (atPoint : before.pp = some point) (extended : ExtT after cx.fn.blocks)
    (target : ∃ block, cx.fn.blocks[header]? = some block ∧ block.params = []) :
    ∀ fuel, DemandInstructionStep cx fuel ⟨point, frame, state⟩ ⟨(header, 0), frame, state⟩ := by
  obtain ⟨_, _, _, instruction⟩ := emitTerm_facts lowered atPoint extended
  obtain ⟨block, blockAt, parameters⟩ := target
  let branch : DemandBranch := .jump header []
  have branchAt : instAt cx.fn point = some (.term branch.term) := by
    simpa only [instAt_eq, branch, DemandBranch.term] using instruction
  have execution : branch.enter cx.fn frame state = .ok (header, instsAt cx.fn (header, 0), frame) state := by
    simp [branch, DemandBranch.enter, mapList, enterBlock, blockAt, parameters, bindParams, instsAt, bind_apply, pure_apply]
  exact fun fuel => .control branchAt execution

#print axioms generated_while_back_edge
end Goose.Lower

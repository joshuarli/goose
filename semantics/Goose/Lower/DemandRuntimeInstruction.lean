import Goose.Lower.DemandRunAtPrefix
import Goose.GIR.Sound

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem terminated_first_instruction {fn : Func} {blockId : BlockId} {block : GIR.Block}
    (terminated : TerminatedBlocks fn) (blockAt : fn.blocks[blockId]? = some block) :
    ∃ instruction, instAt fn (blockId, 0) = some instruction := by
  have last := (terminated block (Array.mem_of_getElem? blockAt)).2
  have nonempty : block.insts ≠ [] := by
    intro empty
    simp [Block.lastTerm?, empty] at last
  have bound : 0 < block.insts.length := List.length_pos_iff.mpr nonempty
  exact ⟨block.insts[0], by simp [instAt, blockAt, bound]⟩

theorem terminated_instruction_after_nonterm {fn : Func} {point : Pt} {instruction : Inst}
    (terminated : TerminatedBlocks fn) (atPoint : instAt fn point = some instruction)
    (notTerm : ∀ term, instruction ≠ .term term) :
    ∃ next, instAt fn (point.1, point.2 + 1) = some next := by
  unfold instAt at atPoint
  cases blockAt : fn.blocks[point.1]? with
  | none => simp [blockAt] at atPoint
  | some block =>
    simp only [blockAt, Option.bind_some] at atPoint
    have last := (terminated block (Array.mem_of_getElem? blockAt)).2
    cases lastAt : block.insts.getLast? with
    | none => simp [Block.lastTerm?, lastAt] at last
    | some final =>
      cases final with
      | «def» _ _ => simp [Block.lastTerm?, lastAt] at last
      | eff _ => simp [Block.lastTerm?, lastAt] at last
      | term term =>
        obtain ⟨earlier, shape⟩ := List.getLast?_eq_some_iff.mp lastAt
        have bound := (List.getElem?_eq_some_iff.mp atPoint).1
        have earlierBound : point.2 < earlier.length := by
          by_cases earlierFact : point.2 < earlier.length
          · exact earlierFact
          · have equal : point.2 = earlier.length := by rw [shape] at bound; simp at bound; omega
            have same : instruction = .term term := by simpa [shape, equal] using atPoint.symm
            exact (notTerm term same).elim
        have nextBound : point.2 + 1 < block.insts.length := by rw [shape]; simp; omega
        exact ⟨block.insts[point.2 + 1], by simp [instAt, blockAt, nextBound]⟩

theorem terminated_entered_instruction {fn : Func} {frame next : GIR.Frame} {target : BlockId} {values : List RVal}
    {state after : St} {insts : List Inst} (terminated : TerminatedBlocks fn)
    (entered : enterBlock fn frame target values state = .ok (insts, next) after) :
    ∃ instruction, instAt fn (target, 0) = some instruction := by
  cases blockAt : fn.blocks[target]? with
  | none => simp [enterBlock, blockAt, fault, M.stop] at entered
  | some block => exact terminated_first_instruction terminated blockAt

theorem RuntimeStep.next_instruction {cx : FnCtx} {before after : DemandRuntimePoint}
    (terminated : TerminatedBlocks cx.fn)
    (step : Evidence.RuntimeStep cx.cfg cx.fn before.point before.frame before.state after.point after.frame after.state) :
    ∃ instruction, instAt cx.fn after.point = some instruction := by
  cases before
  cases after
  cases step with
  | define instruction execution => exact terminated_instruction_after_nonterm terminated instruction (by intro term same; cases same)
  | effect instruction execution => exact terminated_instruction_after_nonterm terminated instruction (by intro term same; cases same)
  | branch instruction read entered => exact terminated_entered_instruction terminated entered
  | branchTrue instruction test read entered => exact terminated_entered_instruction terminated entered
  | branchFalse instruction test read entered => exact terminated_entered_instruction terminated entered

theorem DemandRuntimePrefix.has_instruction {cx : FnCtx} {taken : Nat} {before after : DemandRuntimePoint}
    (terminated : TerminatedBlocks cx.fn) (initial : ∃ instruction, instAt cx.fn before.point = some instruction)
    (steps : DemandRuntimePrefix cx taken before after) :
    ∃ instruction, instAt cx.fn after.point = some instruction := by
  induction steps with
  | zero => exact initial
  | next step rest ih => exact ih (RuntimeStep.next_instruction terminated step)

#print axioms terminated_first_instruction
#print axioms terminated_instruction_after_nonterm
#print axioms RuntimeStep.next_instruction
#print axioms DemandRuntimePrefix.has_instruction
end Goose.Lower

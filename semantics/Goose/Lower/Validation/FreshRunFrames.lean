import Goose.Lower.GeneratedTargetFramesSource
import Goose.Lower.Validation.FreshRunClosure

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem fresh_block_not_loop_target {loop : Option LoopCtx} {before : LS} {target : BlockId}
    (frames : LoopBuilderFrames loop before) (fresh : before.blocks.size ≤ target) :
    ¬ LoopBuilderFrameTarget loop target := by
  intro targeted
  exact Nat.not_lt_of_ge fresh (frames.targetBound targeted)

theorem TermEdgesFramed.term_to_fresh_block {loop : Option LoopCtx} {before captured after : LS}
    (frames : LoopBuilderFrames loop before) {target : BlockId}
    (fresh : before.blocks.size ≤ target) (capturedBound : target < captured.blocks.size)
    (framed : TermEdgesFramed loop captured after)
    {source : BlockId} {body : BlockB} {term : Term}
    (row : after.blocks[source]? = some body) (member : Inst.term term ∈ body.insts.toList)
    (successor : target ∈ term.successors) :
    ∃ old, captured.blocks[source]? = some old ∧ Inst.term term ∈ old.insts.toList := by
  rcases framed source body term target row member successor capturedBound with old | loopTarget
  · exact old
  · exact False.elim (fresh_block_not_loop_target frames fresh loopTarget)

theorem edgeArgsTo_successor {term : Term} {target : BlockId} {args : List ValueId}
    (member : args ∈ edgeArgsTo term target) : target ∈ term.successors := by
  cases term <;> simp only [edgeArgsTo, Term.successors] at member ⊢
  all_goals repeat' first | split at member | simp_all

theorem incomingValues_has_term {func : Func} {target : BlockId} {index : Nat} {value : ValueId}
    (incoming : value ∈ incomingValues func target index) :
    ∃ block ∈ func.blocks.toList, ∃ term args,
      block.lastTerm? = some term ∧ args ∈ edgeArgsTo term target ∧ args[index]? = some value := by
  obtain ⟨block, blockMember, incoming⟩ := List.mem_flatMap.mp incoming
  cases last : block.lastTerm? with
  | none => simp [last] at incoming
  | some term =>
    simp only [last] at incoming
    obtain ⟨args, edge, row⟩ := List.mem_filterMap.mp incoming
    exact ⟨block, blockMember, term, args, last, edge, row⟩

theorem incomingValues_from_framed {loop : Option LoopCtx} {before captured after : LS}
    (frames : LoopBuilderFrames loop before) {target : BlockId}
    (fresh : before.blocks.size ≤ target) (capturedBound : target < captured.blocks.size)
    (framed : TermEdgesFramed loop captured after)
    {func : Func} (blocks : func.blocks = finishBlocks after.blocks)
    {index : Nat} {value : ValueId} (incoming : value ∈ incomingValues func target index) :
    ∃ (source : BlockId) (old : BlockB) (term : Term) (args : List ValueId), captured.blocks[source]? = some old ∧
      Inst.term term ∈ old.insts.toList ∧ args ∈ edgeArgsTo term target ∧ args[index]? = some value := by
  obtain ⟨block, blockMember, term, args, last, edge, valueAt⟩ := incomingValues_has_term incoming
  obtain ⟨source, sourceAt⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp blockMember)
  rw [blocks] at sourceAt
  simp only [finishBlocks, Array.getElem?_map] at sourceAt
  cases bodyAt : after.blocks[source]? with
  | none => simp [bodyAt] at sourceAt
  | some body =>
    simp only [bodyAt, Option.map_some, Option.some.injEq] at sourceAt
    subst block
    have termMember : Inst.term term ∈ body.insts.toList := by
      unfold GIR.Block.lastTerm? at last
      cases lastAt : body.insts.toList.getLast? with
      | none => simp [lastAt] at last
      | some inst =>
        cases inst <;> simp only [lastAt] at last
        all_goals try contradiction
        rename_i finalTerm
        have same : finalTerm = term := Option.some.inj last
        subst finalTerm
        exact List.mem_of_getLast? lastAt
    obtain ⟨old, oldAt, oldMember⟩ := TermEdgesFramed.term_to_fresh_block frames fresh capturedBound framed
      bodyAt termMember (edgeArgsTo_successor edge)
    exact ⟨source, old, term, args, oldAt, oldMember, edge, valueAt⟩

end Goose.Lower.Validation

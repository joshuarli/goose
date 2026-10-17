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

theorem closedBlock_term_is_last {body : BlockB} (closed : ClosedBlock body) {term : Term}
    (member : Inst.term term ∈ body.insts.toList) : (cfgBlock body).lastTerm? = some term := by
  obtain ⟨last, lastAt⟩ := Option.isSome_iff_exists.mp closed.2
  have lastMember : Inst.term last ∈ body.insts.toList := by
    unfold GIR.Block.lastTerm? cfgBlock at lastAt
    cases row : body.insts.toList.getLast? with
    | none => simp [row] at lastAt
    | some inst =>
      cases inst <;> simp only [row] at lastAt
      all_goals try contradiction
      rename_i actual
      have same : actual = last := Option.some.inj lastAt
      subst actual
      exact List.mem_of_getLast? row
  have termMember : term ∈ (cfgBlock body).terms :=
    List.mem_filterMap.mpr ⟨.term term, member, rfl⟩
  have lastTermMember : last ∈ (cfgBlock body).terms :=
    List.mem_filterMap.mpr ⟨.term last, lastMember, rfl⟩
  obtain ⟨only, terms⟩ := List.length_eq_one_iff.mp closed.1
  rw [terms] at termMember lastTermMember
  have same : last = term := (List.mem_singleton.mp lastTermMember).trans (List.mem_singleton.mp termMember).symm
  exact same ▸ lastAt

theorem incomingValues_retains_branch {captured after : LS} (extension : captured.Ext after)
    (closed : ∀ body ∈ after.blocks.toList, ClosedBlock body)
    {source target : BlockId} {old : BlockB} {args : List ValueId}
    (sourceAt : captured.blocks[source]? = some old) (branch : Inst.term (.br target args) ∈ old.insts.toList)
    {func : Func} (blocks : func.blocks = finishBlocks after.blocks)
    {index : Nat} {value : ValueId} (argument : args[index]? = some value) :
    value ∈ incomingValues func target index := by
  obtain ⟨body, bodyAt, _, extra, append⟩ := extension.2 source old sourceAt
  have retained : Inst.term (.br target args) ∈ body.insts.toList := by
    rw [append]
    exact List.mem_append_left _ branch
  have bodyMember : body ∈ after.blocks.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? bodyAt)
  have last := closedBlock_term_is_last (closed body bodyMember) retained
  apply List.mem_flatMap.mpr
  refine ⟨cfgBlock body, ?_, ?_⟩
  · rw [blocks]
    simpa only [finishBlocks, cfgBlock, Array.toList_map, List.mem_map] using
      (List.mem_map.mpr ⟨body, bodyMember, rfl⟩ : cfgBlock body ∈ after.blocks.toList.map cfgBlock)
  · simp only [last]
    apply List.mem_filterMap.mpr
    exact ⟨args, by simp [edgeArgsTo], argument⟩

theorem freshLiteralValue_of_framed {loop : Option LoopCtx} {before captured after : LS}
    (frames : LoopBuilderFrames loop before) {target : BlockId}
    (fresh : before.blocks.size ≤ target) (capturedBound : target < captured.blocks.size)
    (framed : TermEdgesFramed loop captured after) (extension : captured.Ext after)
    (closed : ∀ body ∈ after.blocks.toList, ClosedBlock body)
    {func : Func} {types : Array (Option VTy)} (blocks : func.blocks = finishBlocks after.blocks)
    {value : ValueId} {ty : VTy} {index : Nat} (targetBound : target < func.blocks.size)
    (parameter : func.blocks[target].params[index]? = some (value, ty))
    {source : BlockId} {old : BlockB} {args : List ValueId} {input : ValueId}
    (sourceAt : captured.blocks[source]? = some old) (branch : Inst.term (.br target args) ∈ old.insts.toList)
    (argument : args[index]? = some input)
    (inputs : ∀ (source : BlockId) (old : BlockB) (term : Term) (args : List ValueId) (input : ValueId),
      captured.blocks[source]? = some old → Inst.term term ∈ old.insts.toList →
      args ∈ edgeArgsTo term target → args[index]? = some input → FreshLiteralValue func types input) :
    FreshLiteralValue func types value := by
  have retained := incomingValues_retains_branch extension closed sourceAt branch blocks argument
  apply FreshLiteralValue.parameter targetBound parameter
  · intro empty
    simp [empty] at retained
  · intro input incoming
    obtain ⟨source, old, term, args, row, member, edge, argument⟩ :=
      incomingValues_from_framed frames fresh capturedBound framed blocks incoming
    exact inputs source old term args input row member edge argument

end Goose.Lower.Validation

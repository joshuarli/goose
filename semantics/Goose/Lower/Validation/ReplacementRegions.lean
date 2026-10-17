import Goose.Lower.Validation.ReplacementIndependence
import Goose.Lower.Validation.FreshRunFrames

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem closedBlock_append_eq {before after : BlockB} (oldClosed : ClosedBlock before)
    (newClosed : ClosedBlock after) {extra : List Inst}
    (append : after.insts.toList = before.insts.toList ++ extra) : extra = [] := by
  have noTerms : extra.filterMap Inst.term? = [] := by
    have lengths := newClosed.1
    simp only [cfgBlock, GIR.Block.terms, append, List.filterMap_append, List.length_append] at lengths
    have oldLength := oldClosed.1
    change (before.insts.toList.filterMap Inst.term?).length = 1 at oldLength
    apply List.eq_nil_of_length_eq_zero
    omega
  cases lastAt : extra.getLast? with
  | none => exact List.getLast?_eq_none_iff.mp lastAt
  | some inst =>
    have last := newClosed.2
    simp only [cfgBlock, GIR.Block.lastTerm?, append, List.getLast?_append, lastAt, Option.or_some] at last
    cases inst with
    | «def» value op => simp [Option.or] at last
    | eff effect => simp [Option.or] at last
    | term term =>
      have member : term ∈ extra.filterMap Inst.term? :=
        List.mem_filterMap.mpr ⟨.term term, List.mem_of_getLast? lastAt, rfl⟩
      simp [noTerms] at member

theorem transferEmptyEdge_retains (func : Func) (facts : List ValueId) (target : BlockId)
    (args : List ValueId) : facts ⊆ transferEmptyEdge func facts target args := by
  unfold transferEmptyEdge
  cases row : func.blocks[target]? with
  | none => exact fun _ member => member
  | some block =>
    dsimp only
    apply List.foldlRecOn (motive := fun current => facts ⊆ current)
    · exact fun _ member => member
    · intro current subset item member value known
      split
      · exact List.mem_append_left _ (subset known)
      · exact subset known

theorem transferEmptyBlock_contains_clear {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {owner : ValueId} {origin : Option OriginId} {block : GIR.Block}
    {head tail : List Inst} (split : block.insts = head ++ (.eff (.clear owner origin) :: tail))
    (apart : ∀ inst ∈ tail, ReplacementInstApart module types queries owner inst)
    (facts : List ValueId) : owner ∈ transferEmptyBlock module types queries facts block := by
  unfold transferEmptyBlock
  rw [split, List.foldl_append, List.foldl_cons]
  exact transferEmptyBlock_retains_of_apart (block := ⟨[], tail⟩) apart
    (transferEmptyInst_clear_has_owner module types queries _ owner origin)

def ReplacementRegionFacts (before captured : LS) (owner : ValueId) (block : BlockId) : List ValueId :=
  if before.blocks.size ≤ block ∧ block < captured.blocks.size then [owner] else []

theorem replacementRegionFacts_entry {before captured : LS} {owner : ValueId}
    (nonempty : 0 < before.blocks.size) : ReplacementRegionFacts before captured owner 0 = [] := by
  simp [ReplacementRegionFacts, Nat.not_le_of_gt nonempty]

theorem finishBlocks_row_source {state : LS} {func : Func}
    (blocks : func.blocks = finishBlocks state.blocks) {index : BlockId} {block : GIR.Block}
    (row : func.blocks[index]? = some block) :
    ∃ body, state.blocks[index]? = some body ∧ cfgBlock body = block := by
  rw [blocks] at row
  simp only [finishBlocks, Array.getElem?_map] at row
  cases bodyAt : state.blocks[index]? with
  | none => simp [bodyAt] at row
  | some body =>
    simp only [bodyAt, Option.map_some, Option.some.injEq] at row
    exact ⟨body, rfl, row⟩

theorem termEdges_successor {term : Term} {target : BlockId} {args : List ValueId}
    (edge : (target, args) ∈ termEdges term) : target ∈ term.successors := by
  cases term <;> simp_all [termEdges, Term.successors]
  rcases edge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem closedTerm_row_retained {before after : LS} (extension : before.Ext after)
    (shaped : ∀ (index : BlockId) (body : BlockB), before.blocks[index]? = some body → OpenBlock body ∨ ClosedBlock body)
    (closed : ∀ body ∈ after.blocks.toList, ClosedBlock body)
    {index : BlockId} {old final : BlockB} {term : Term}
    (oldAt : before.blocks[index]? = some old) (finalAt : after.blocks[index]? = some final)
    (member : Inst.term term ∈ old.insts.toList) : final.insts.toList = old.insts.toList := by
  have oldClosed : ClosedBlock old := by
    rcases shaped index old oldAt with opened | finished
    · have termMember : term ∈ (cfgBlock old).terms :=
        List.mem_filterMap.mpr ⟨.term term, member, rfl⟩
      simp only [OpenBlock] at opened
      simp [opened] at termMember
    · exact finished
  have finalClosed := closed final (Array.mem_toList_iff.mpr (Array.mem_of_getElem? finalAt))
  obtain ⟨next, nextAt, _, extra, append⟩ := extension.2 index old oldAt
  have same : next = final := Option.some.inj (nextAt.symm.trans finalAt)
  subst next
  have empty := closedBlock_append_eq oldClosed finalClosed append
  simpa only [empty, List.append_nil] using append

theorem replacementRegion_closed {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {owner : ValueId} {before captured after : LS}
    (advance : before.Adv captured) (bounded : TargetsBounded before)
    {loop : Option LoopCtx} (frames : LoopBuilderFrames loop before)
    (framed : TermEdgesFramed loop captured after) (extension : captured.Ext after)
    (shaped : ∀ (index : BlockId) (body : BlockB), captured.blocks[index]? = some body → OpenBlock body ∨ ClosedBlock body)
    (closed : ∀ body ∈ after.blocks.toList, ClosedBlock body)
    {func : Func} (blocks : func.blocks = finishBlocks after.blocks)
    (newApart : ∀ (index : BlockId) (body : BlockB), captured.blocks[index]? = some body → before.blocks.size ≤ index →
      ∀ inst ∈ body.insts.toList, ReplacementInstApart module types queries owner inst)
    (startClear : ∀ (index : BlockId) (body : BlockB), before.cur = some index → captured.blocks[index]? = some body →
      ∃ head tail origin, body.insts.toList = head ++ (.eff (.clear owner origin) :: tail) ∧
        ∀ inst ∈ tail, ReplacementInstApart module types queries owner inst) :
    EmptyFactsClosed module func types queries (ReplacementRegionFacts before captured owner) := by
  intro source block blockAt target args edge value required
  unfold ReplacementRegionFacts at required
  split at required
  · rename_i range
    obtain ⟨lower, upper⟩ := range
    have sameOwner : value = owner := List.mem_singleton.mp required
    subst value
    obtain ⟨term, termMember, termEdge⟩ := List.mem_flatMap.mp edge
    have instMember : Inst.term term ∈ block.insts := by
      obtain ⟨inst, instMember, termAt⟩ := List.mem_filterMap.mp termMember
      cases inst with
      | «def» value op => simp [Inst.term?] at termAt
      | eff effect => simp [Inst.term?] at termAt
      | term actual =>
        have same : actual = term := Option.some.inj termAt
        exact same ▸ instMember
    obtain ⟨finalBody, finalAt, blockEq⟩ := finishBlocks_row_source blocks blockAt
    subst block
    obtain ⟨old, oldAt, oldMember⟩ := TermEdgesFramed.term_to_fresh_block frames lower upper framed
      finalAt instMember (termEdges_successor termEdge)
    have unchanged := closedTerm_row_retained extension shaped closed oldAt finalAt oldMember
    have outgoing : owner ∈ transferEmptyBlock module types queries
        (ReplacementRegionFacts before captured owner source) (cfgBlock finalBody) := by
      by_cases previous : source < before.blocks.size
      · by_cases selected : before.cur = some source
        · obtain ⟨head, tail, origin, split, apart⟩ := startClear source old selected oldAt
          apply transferEmptyBlock_contains_clear (head := head) (tail := tail) (origin := origin)
          · change finalBody.insts.toList = _
            exact unchanged.trans split
          · exact apart
        · let previousBody := before.blocks[source]
          have previousAt : before.blocks[source]? = some previousBody := by simp [previousBody, previous]
          have kept := advance.keep source previousBody selected previousAt
          have same : previousBody = old := Option.some.inj (kept.symm.trans oldAt)
          have oldBeforeAt : before.blocks[source]? = some old := previousAt.trans (congrArg some same)
          have targetBound : target < before.blocks.size := bounded source old oldBeforeAt target (by
            apply List.mem_flatMap.mpr
            exact ⟨term, List.mem_filterMap.mpr ⟨.term term, oldMember, rfl⟩, termEdges_successor termEdge⟩)
          exact False.elim (Nat.not_lt_of_ge lower targetBound)
      · have sourceLower : before.blocks.size ≤ source := Nat.le_of_not_gt previous
        have sourceUpper : source < captured.blocks.size := (Array.getElem?_eq_some_iff.mp oldAt).1
        have apart : ∀ inst ∈ (cfgBlock finalBody).insts, ReplacementInstApart module types queries owner inst := by
          intro inst member
          apply newApart source old oldAt sourceLower
          simpa only [cfgBlock, unchanged] using member
        apply transferEmptyBlock_retains_of_apart apart
        simp [ReplacementRegionFacts, sourceLower, sourceUpper]
    exact transferEmptyEdge_retains func _ target args outgoing
  · simp at required

end Goose.Lower.Validation

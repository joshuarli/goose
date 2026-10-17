import Goose.Lower.Validation.ReplacementScan

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem killEmptyFacts_mono {before after : List ValueId} (subset : before ⊆ after)
    (roots : ReplacementRootQuery) (queries : ReplacementQueries) :
    killEmptyFacts before roots queries ⊆ killEmptyFacts after roots queries := by
  intro value member
  obtain ⟨present, independent⟩ := List.mem_filter.mp member
  exact List.mem_filter.mpr ⟨subset present, independent⟩

theorem killEmptyFactSources_mono {before after : List ValueId} (subset : before ⊆ after)
    (operands : List ValueId) (types : Array (Option VTy)) (queries : ReplacementQueries) :
    killEmptyFactSources before operands types queries ⊆ killEmptyFactSources after operands types queries := by
  induction operands generalizing before after with
  | nil => exact subset
  | cons operand rest ih =>
    unfold killEmptyFactSources
    simp only [List.foldl_cons]
    apply ih
    split
    · exact killEmptyFacts_mono subset _ _
    · exact subset

theorem clearFacts_mono {before after : List ValueId} (subset : before ⊆ after) (owner : ValueId) :
    (if before.contains owner then before else before ++ [owner]) ⊆
      (if after.contains owner then after else after ++ [owner]) := by
  intro value member
  by_cases old : before.contains owner = true <;> by_cases next : after.contains owner = true
  · simpa only [old, next, ite_true] using subset (by simpa only [old, ite_true] using member)
  · simp only [old, next, ite_true, Bool.false_eq_true, ite_false] at member ⊢
    exact List.mem_append_left _ (subset member)
  · simp only [old, next, Bool.false_eq_true, ite_false, ite_true] at member ⊢
    rcases List.mem_append.mp member with previous | fresh
    · exact subset previous
    · have same := List.mem_singleton.mp fresh
      exact same ▸ List.contains_iff_mem.mp next
  · simp only [old, next, Bool.false_eq_true, ite_false] at member ⊢
    rcases List.mem_append.mp member with previous | fresh
    · exact List.mem_append_left _ (subset previous)
    · exact List.mem_append_right _ fresh

theorem transferEmptyInst_mono (module : GIR.Module) (types : Array (Option VTy))
    (queries : ReplacementQueries) (inst : Inst) {before after : List ValueId}
    (subset : before ⊆ after) :
    transferEmptyInst module types queries before inst ⊆ transferEmptyInst module types queries after inst := by
  cases inst with
  | «def» value op =>
    cases op <;> dsimp only [transferEmptyInst]
    all_goals
      repeat' first
      | exact subset
      | exact killEmptyFacts_mono subset _ _
      | exact killEmptyFactSources_mono subset _ _ _
      | apply killEmptyFacts_mono
      | apply killEmptyFactSources_mono
      | split
  | eff effect =>
    cases effect <;> dsimp only [transferEmptyInst]
    all_goals
      repeat' first
      | exact subset
      | exact clearFacts_mono subset _
      | exact killEmptyFacts_mono subset _ _
      | exact killEmptyFactSources_mono subset _ _ _
      | apply killEmptyFacts_mono
      | apply killEmptyFactSources_mono
      | split
  | term term => exact killEmptyFactSources_mono subset _ _ _

theorem transferEmptyBlock_mono (module : GIR.Module) (types : Array (Option VTy))
    (queries : ReplacementQueries) (block : GIR.Block) {before after : List ValueId}
    (subset : before ⊆ after) :
    transferEmptyBlock module types queries before block ⊆ transferEmptyBlock module types queries after block := by
  unfold transferEmptyBlock
  induction block.insts generalizing before after with
  | nil => exact subset
  | cons inst rest ih =>
    simp only [List.foldl_cons]
    exact ih (transferEmptyInst_mono module types queries inst subset)

theorem edgeFactStep_mono {before after : List ValueId} (subset : before ⊆ after)
    (parameter argument : ValueId) :
    (if before.contains argument && !before.contains parameter then before ++ [parameter] else before) ⊆
      (if after.contains argument && !after.contains parameter then after ++ [parameter] else after) := by
  intro value member
  have retains : after ⊆ (if after.contains argument && !after.contains parameter
      then after ++ [parameter] else after) := by
    split
    · exact fun _ member => List.mem_append_left _ member
    · exact fun _ member => member
  split at member
  · rename_i old
    rcases List.mem_append.mp member with previous | fresh
    · exact retains (subset previous)
    · have same := List.mem_singleton.mp fresh
      subst value
      by_cases present : after.contains parameter = true
      · exact retains (List.contains_iff_mem.mp present)
      · have argBefore : argument ∈ before := by
          have parts : before.contains argument = true ∧ before.contains parameter = false := by simpa using old
          exact List.contains_iff_mem.mp parts.1
        have argAfter : after.contains argument = true := List.contains_iff_mem.mpr (subset argBefore)
        simp only [argAfter, Bool.eq_false_iff.mpr present, Bool.not_false, Bool.and_self, ite_true]
        exact List.mem_append_right _ (by simp)
  · exact retains (subset member)

theorem transferEmptyEdge_mono (func : Func) (target : BlockId) (args : List ValueId)
    {before after : List ValueId} (subset : before ⊆ after) :
    transferEmptyEdge func before target args ⊆ transferEmptyEdge func after target args := by
  unfold transferEmptyEdge
  cases row : func.blocks[target]? with
  | none => exact subset
  | some block =>
    dsimp only
    generalize block.params.zip args = items
    induction items generalizing before after with
    | nil => exact subset
    | cons item rest ih =>
      obtain ⟨⟨parameter, ty⟩, argument⟩ := item
      simp only [List.foldl_cons]
      exact ih (edgeFactStep_mono subset parameter argument)

def RequiredEmptyFacts (required : BlockId → List ValueId)
    (states : Array (Option (List ValueId))) : Prop :=
  ∀ index facts, states[index]? = some (some facts) → required index ⊆ facts

theorem requiredEmptyFacts_set {required : BlockId → List ValueId}
    {states : Array (Option (List ValueId))} (checked : RequiredEmptyFacts required states)
    {index : BlockId} {facts : List ValueId} (known : required index ⊆ facts) :
    RequiredEmptyFacts required (states.set! index (some facts)) := by
  intro other previous row
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at row
  split at row
  · rename_i same
    subst other
    split at row
    · have same := Option.some.inj (Option.some.inj row)
      subst previous
      exact known
    · cases row
  · exact checked other previous row

def EmptyFactsClosed (module : GIR.Module) (func : Func) (types : Array (Option VTy))
    (queries : ReplacementQueries) (required : BlockId → List ValueId) : Prop :=
  ∀ source block, func.blocks[source]? = some block →
    ∀ target args, (target, args) ∈ block.terms.flatMap termEdges →
      required target ⊆ transferEmptyEdge func
        (transferEmptyBlock module types queries (required source) block) target args

theorem emptyFactRound_required (module : GIR.Module) (func : Func) (types : Array (Option VTy))
    (queries : ReplacementQueries) (required : BlockId → List ValueId)
    (closed : EmptyFactsClosed module func types queries required)
    (states : Array (Option (List ValueId))) (checked : RequiredEmptyFacts required states) :
    RequiredEmptyFacts required (emptyFactRound module func types queries states).1 := by
  unfold emptyFactRound
  change RequiredEmptyFacts required
    ((forIn' (m := Id) [:func.blocks.size] (states, false) _).1)
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply list_forIn'_invariant (property := fun current : Array (Option (List ValueId)) × Bool =>
    RequiredEmptyFacts required current.1)
  · exact checked
  · intro source member current valid
    dsimp only
    split
    · rename_i block blockAt
      split
      · rename_i incoming incomingAt
        have sourceRequired := checked source incoming (Option.join_eq_some_iff.mp incomingAt)
        apply list_forIn_member_invariant (property := fun current : Array (Option (List ValueId)) × Bool =>
          RequiredEmptyFacts required current.1)
        · exact valid
        · intro edge edgeMember current valid
          obtain ⟨target, args⟩ := edge
          have requiredEdge : required target ⊆ transferEmptyEdge func
              (transferEmptyBlock module types queries incoming block) target args :=
            fun _ member => transferEmptyEdge_mono func target args
              (transferEmptyBlock_mono module types queries block sourceRequired)
              (closed source block blockAt target args edgeMember member)
          dsimp only
          split
          · split
            · exact requiredEmptyFacts_set valid requiredEdge
            · rename_i previous previousAt
              split
              · apply requiredEmptyFacts_set valid
                intro value needed
                exact List.mem_filter.mpr
                  ⟨valid target previous previousAt needed, List.contains_iff_mem.mpr (requiredEdge needed)⟩
              · exact valid
            · exact valid
          · exact valid
      · exact valid
    · exact valid

theorem emptyFactsAtBlocks_required (module : GIR.Module) (func : Func) (types : Array (Option VTy))
    (queries : ReplacementQueries) (required : BlockId → List ValueId)
    (closed : EmptyFactsClosed module func types queries required) (entry : required 0 = [])
    (nonempty : 0 < func.blocks.size) :
    RequiredEmptyFacts required (emptyFactsAtBlocks module func types queries) := by
  have base : RequiredEmptyFacts required (Array.replicate func.blocks.size none) := by
    intro index facts row
    simp only [Array.getElem?_replicate] at row
    split at row <;> cases row
  let seed : Array (Option (List ValueId)) := (Array.replicate func.blocks.size none).set! 0 (some [])
  have seeded : RequiredEmptyFacts required seed := requiredEmptyFacts_set base (by simp [entry])
  have known := dataflowRounds_invariant (emptyFactRound module func types queries)
    (fun states checked => emptyFactRound_required module func types queries required closed states checked)
    seed true ((func.blocks.size + 1) * (func.numValues + 1) + 1) seeded
  have algorithm : emptyFactsAtBlocks module func types queries =
      dataflowRounds (emptyFactRound module func types queries) seed true
        ((func.blocks.size + 1) * (func.numValues + 1) + 1) := by
    have present : func.blocks.isEmpty = false := by simp [Array.isEmpty, Nat.ne_of_gt nonempty]
    unfold emptyFactsAtBlocks
    simp only [present, Bool.not_false, ite_true]
    rfl
  rw [algorithm]
  exact known

theorem lowerContextAt_required_emptyFacts (module : Core.Module) (context : Core.Context)
    (impl : Core.Impl) (types : Array (Option VTy))
    (required : BlockId → List ValueId)
    (closed : EmptyFactsClosed (lower module) (lowerContextAt module context impl) types
      (replacementQueries (lower module) (lowerContextAt module context impl) types) required)
    (entry : required 0 = []) {block : BlockId} (bounded : block < (lowerContextAt module context impl).blocks.size) :
    ∃ facts, (emptyFactsAtBlocks (lower module) (lowerContextAt module context impl) types
      (replacementQueries (lower module) (lowerContextAt module context impl) types))[block]? = some (some facts) ∧
      required block ⊆ facts := by
  obtain ⟨facts, known⟩ := lowerContextAt_emptyFacts_known module context impl types _ bounded
  exact ⟨facts, known, emptyFactsAtBlocks_required _ _ _ _ _ closed entry
    (lowerImpl_blocks_nonempty module impl) block facts known⟩

theorem lowerGlobal_required_emptyFacts (module : Core.Module) (global : Core.Global)
    (types : Array (Option VTy)) (required : BlockId → List ValueId)
    (closed : EmptyFactsClosed (lower module) (lowerGlobal module global).init types
      (replacementQueries (lower module) (lowerGlobal module global).init types) required)
    (entry : required 0 = []) {block : BlockId} (bounded : block < (lowerGlobal module global).init.blocks.size) :
    ∃ facts, (emptyFactsAtBlocks (lower module) (lowerGlobal module global).init types
      (replacementQueries (lower module) (lowerGlobal module global).init types))[block]? = some (some facts) ∧
      required block ⊆ facts := by
  obtain ⟨facts, known⟩ := lowerGlobal_emptyFacts_known module global types _ bounded
  exact ⟨facts, known, emptyFactsAtBlocks_required _ _ _ _ _ closed entry
    (lowerGlobal_blocks_nonempty module global) block facts known⟩

end Goose.Lower.Validation

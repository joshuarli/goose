import Goose.Lower.Validation.ShrinkMeasure
import Goose.Lower.Validation.CfgReachability

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem list_forIn'_establishes {property known : σ → Prop} (items : List α) (start : σ)
    (body : (item : α) → item ∈ items → σ → Id (ForInStep σ))
    (target : α) (member : target ∈ items) (initial : property start)
    (preserved : ∀ item member state, property state → property (body item member state).value)
    (retained : ∀ item member state, known state → known (body item member state).value)
    (yielded : ∀ item member state, ∃ next, body item member state = .yield next)
    (established : ∀ state, property state → known (body target member state).value) :
    known (forIn' items start body) := by
  induction items generalizing start with
  | nil => simp at member
  | cons first rest ih =>
    rw [List.forIn'_cons]
    obtain ⟨mid, run⟩ := yielded first (by simp) start
    rw [run]
    change known (forIn' (m := Id) rest mid (fun item member => body item (by simp [member])))
    rcases List.mem_cons.mp member with equal | inRest
    · subst first
      apply list_forIn'_invariant
      · simpa [run] using established start initial
      · intro item member state checked
        exact retained item (by simp [member]) state checked
    · apply ih mid (fun item member => body item (by simp [member])) inRest
      · simpa [run] using preserved first (by simp) start initial
      · intro item member state checked
        exact preserved item (by simp [member]) state checked
      · intro item member state checked
        exact retained item (by simp [member]) state checked
      · intro item member state
        exact yielded item (by simp [member]) state
      · intro state checked
        exact established state checked

theorem list_forIn_establishes {property known : σ → Prop} (items : List α) (start : σ)
    (body : α → σ → Id (ForInStep σ))
    (target : α) (member : target ∈ items) (initial : property start)
    (preserved : ∀ item state, property state → property (body item state).value)
    (retained : ∀ item state, known state → known (body item state).value)
    (yielded : ∀ item state, ∃ next, body item state = .yield next)
    (established : ∀ state, property state → known (body target state).value) :
    known (forIn items start body) := by
  induction items generalizing start with
  | nil => simp at member
  | cons first rest ih =>
    rw [List.forIn_cons]
    obtain ⟨mid, run⟩ := yielded first start
    rw [run]
    change known (forIn rest mid body)
    rcases List.mem_cons.mp member with equal | inRest
    · subst first
      apply list_forIn_invariant
      · simpa [run] using established start initial
      · exact retained
    · apply ih mid inRest
      · simpa [run] using preserved first start initial

def EmptyStateKnown (states : Array (Option (List ValueId))) (target : BlockId) : Prop :=
  ∃ facts, states[target]? = some (some facts)

theorem KnownStatesPreserved.known {before after : Array (Option (List ValueId))}
    (preserved : KnownStatesPreserved before after) {target : BlockId}
    (known : EmptyStateKnown before target) : EmptyStateKnown after target := by
  obtain ⟨facts, present⟩ := known
  exact preserved.2 target facts present

theorem emptyFactRound_edge_known (module : GIR.Module) (func : Func)
    (types : Array (Option VTy)) (provenance : ReplacementQueries) (states : Array (Option (List ValueId)))
    (size : states.size = func.blocks.size) {source target : BlockId} {body : GIR.Block}
    (sourceAt : func.blocks[source]? = some body) (sourceKnown : EmptyStateKnown states source)
    {args : List ValueId} (edge : (target, args) ∈ body.terms.flatMap termEdges)
    (targetBound : target < func.blocks.size) :
    EmptyStateKnown (emptyFactRound module func types provenance states).1 target := by
  unfold emptyFactRound
  change EmptyStateKnown ((forIn' (m := Id) [:func.blocks.size] (states, false) _).1) target
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  refine list_forIn'_establishes
    (property := fun current : Array (Option (List ValueId)) × Bool => KnownStatesPreserved states current.1)
    (known := fun current : Array (Option (List ValueId)) × Bool => EmptyStateKnown current.1 target)
    _ _ _ source ?_ ?_ ?_ ?_ ?_ ?_
  · have sourceBound := (Array.getElem?_eq_some_iff.mp sourceAt).1
    simpa [Std.Legacy.Range.size] using sourceBound
  · exact .refl states
  · intro block member current checked
    dsimp only
    split
    · split
      · apply list_forIn_invariant (property := fun current : Array (Option (List ValueId)) × Bool =>
          KnownStatesPreserved states current.1)
        · exact checked
        · intro edge current checked
          obtain ⟨next, args⟩ := edge
          dsimp only
          split
          · split
            · exact checked.trans (knownStates_set _ _ _)
            · split
              · exact checked.trans (knownStates_set _ _ _)
              · exact checked
            · exact checked
          · exact checked
      · exact checked
    · exact checked
  · intro block member current checked
    dsimp only
    split
    · split
      · apply list_forIn_invariant (property := fun current : Array (Option (List ValueId)) × Bool =>
          EmptyStateKnown current.1 target)
        · exact checked
        · intro edge current checked
          obtain ⟨next, args⟩ := edge
          dsimp only
          split
          · split
            · exact (knownStates_set _ _ _).known checked
            · split
              · exact (knownStates_set _ _ _).known checked
              · exact checked
            · exact checked
          · exact checked
      · exact checked
    · exact checked
  · intro block member current
    dsimp only
    split
    · split <;> exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · intro current checked
    obtain ⟨facts, factsAt⟩ := sourceKnown
    have joined : states[source]?.join = some facts := by rw [factsAt]; rfl
    dsimp only
    rw [sourceAt, joined]
    apply list_forIn_establishes (target := (target, args)) (member := edge)
      (property := fun current : Array (Option (List ValueId)) × Bool => KnownStatesPreserved states current.1)
      (known := fun current : Array (Option (List ValueId)) × Bool => EmptyStateKnown current.1 target)
    · exact checked
    · intro edge current checked
      obtain ⟨next, args⟩ := edge
      dsimp only
      split
      · split
        · exact checked.trans (knownStates_set _ _ _)
        · split
          · exact checked.trans (knownStates_set _ _ _)
          · exact checked
        · exact checked
      · exact checked
    · intro edge current checked
      obtain ⟨next, args⟩ := edge
      dsimp only
      split
      · split
        · exact (knownStates_set _ _ _).known checked
        · split
          · exact (knownStates_set _ _ _).known checked
          · exact checked
        · exact checked
      · exact checked
    · intro edge current
      obtain ⟨next, args⟩ := edge
      dsimp only
      split
      · split
        · exact ⟨_, rfl⟩
        · split <;> exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · intro current checked
      have bounded : target < current.1.size := by rw [checked.1, size]; exact targetBound
      dsimp only
      simp only [bounded, ite_true]
      split
      · change ∃ facts, (current.1.setIfInBounds target (_))[target]? = some (some facts)
        rw [Array.getElem?_setIfInBounds]
        exact ⟨transferEmptyEdge func (transferEmptyBlock module types provenance facts body) target args,
          by simp [bounded]⟩
      · rename_i previous lookup
        split
        · change ∃ facts, (current.1.setIfInBounds target _)[target]? = some (some facts)
          rw [Array.getElem?_setIfInBounds]
          exact ⟨previous.filter (transferEmptyEdge func (transferEmptyBlock module types provenance facts body) target args).contains,
            by simp [bounded]⟩
        · exact ⟨previous, lookup⟩
      · rename_i missing
        have outside := Array.getElem?_eq_none_iff.mp missing
        nat_omega

theorem emptyFactsAtBlocks_size (module : GIR.Module) (func : Func)
    (types : Array (Option VTy)) (provenance : ReplacementQueries) (nonempty : 0 < func.blocks.size) :
    (emptyFactsAtBlocks module func types provenance).size = func.blocks.size := by
  rw [emptyFactsAtBlocks_eq_rounds module func types provenance nonempty]
  apply dataflowRounds_invariant (property := fun states : Array (Option (List ValueId)) => states.size = func.blocks.size)
  · intro states size
    exact (emptyFactRound_preserves_known module func types provenance states).1.trans size
  · simp

theorem emptyFactsAtBlocks_edge_known (module : GIR.Module) (func : Func)
    (types : Array (Option VTy)) (provenance : ReplacementQueries) (nonempty : 0 < func.blocks.size)
    (operands : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      ∀ value ∈ inst.uses, value < func.numValues)
    (parameters : ∀ block ∈ func.blocks.toList, ∀ param ∈ block.params, param.1 < func.numValues)
    {source target : BlockId} {body : GIR.Block} (sourceAt : func.blocks[source]? = some body)
    (sourceKnown : EmptyStateKnown (emptyFactsAtBlocks module func types provenance) source)
    {args : List ValueId} (edge : (target, args) ∈ body.terms.flatMap termEdges)
    (targetBound : target < func.blocks.size) :
    EmptyStateKnown (emptyFactsAtBlocks module func types provenance) target := by
  have known := emptyFactRound_edge_known module func types provenance _
    (emptyFactsAtBlocks_size module func types provenance nonempty) sourceAt sourceKnown edge targetBound
  rw [(emptyFactsAtBlocks_stable module func types provenance nonempty operands parameters).2] at known
  exact known

theorem successor_has_edge (term : Term) {target : BlockId} (successor : target ∈ term.successors) :
    ∃ args, (target, args) ∈ termEdges term := by
  cases term with
  | br destination args =>
    have equal : target = destination := by simpa [Term.successors] using successor
    subst target
    exact ⟨args, by simp [termEdges]⟩
  | condbr value left leftArgs right rightArgs =>
    have either : target = left ∨ target = right := by simpa [Term.successors] using successor
    rcases either with rfl | rfl
    · exact ⟨leftArgs, by simp [termEdges]⟩
    · exact ⟨rightArgs, by simp [termEdges]⟩
  | ret values origin => simp [Term.successors] at successor
  | abort kind origin => simp [Term.successors] at successor
  | unreachable => simp [Term.successors] at successor
  | exit value origin => simp [Term.successors] at successor

theorem emptyFactsAtBlocks_known_of_reachable (module : GIR.Module) (func : Func)
    (types : Array (Option VTy)) (provenance : ReplacementQueries) (nonempty : 0 < func.blocks.size)
    (operands : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      ∀ value ∈ inst.uses, value < func.numValues)
    (parameters : ∀ block ∈ func.blocks.toList, ∀ param ∈ block.params, param.1 < func.numValues)
    {block : BlockId} (path : BlockReachable func block) :
    EmptyStateKnown (emptyFactsAtBlocks module func types provenance) block := by
  induction path with
  | entry => exact emptyFactsAtBlocks_entry_known module func types provenance nonempty
  | next prior row successor bounded known =>
    obtain ⟨term, member, targetMember⟩ := List.mem_flatMap.mp successor
    obtain ⟨args, edge⟩ := successor_has_edge term targetMember
    exact emptyFactsAtBlocks_edge_known module func types provenance nonempty operands parameters
      row known (List.mem_flatMap.mpr ⟨term, member, edge⟩) bounded

end Goose.Lower.Validation

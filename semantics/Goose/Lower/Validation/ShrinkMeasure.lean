import Goose.Lower.Validation.ShrinkFacts

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def EmptyStatesWithin (limit : Nat) (states : Array (Option (List ValueId))) : Prop :=
  ∀ (index : Nat) facts, states[index]? = some (some facts) → EmptyFactsWithin limit facts

def emptyStateWeight (limit : Nat) : Option (List ValueId) → Nat
  | none => limit + 1
  | some facts => facts.length

def emptyStateMeasure (limit : Nat) (states : Array (Option (List ValueId))) : Nat :=
  (states.toList.map (emptyStateWeight limit)).sum

private theorem map_sum_set {items : List α} (weight : α → Nat) {index : Nat} {old : α}
    (lookup : items[index]? = some old) (next : α) :
    ((items.set index next).map weight).sum + weight old = (items.map weight).sum + weight next := by
  induction items generalizing index with
  | nil => simp at lookup
  | cons first rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
      subst old
      simp [Nat.add_comm, Nat.add_left_comm]
    | succ index =>
      simp only [List.getElem?_cons_succ] at lookup
      have tail := ih lookup
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
      omega

theorem emptyStateMeasure_set {limit : Nat} {states : Array (Option (List ValueId))}
    {index : Nat} {old : Option (List ValueId)} (lookup : states[index]? = some old)
    (facts : List ValueId) :
    emptyStateMeasure limit (states.set! index (some facts)) + emptyStateWeight limit old =
      emptyStateMeasure limit states + facts.length := by
  unfold emptyStateMeasure
  rw [Array.toList_set!]
  exact map_sum_set (emptyStateWeight limit) (by simpa using lookup) (some facts)

theorem EmptyStatesWithin.set {limit : Nat} {states : Array (Option (List ValueId))}
    (checked : EmptyStatesWithin limit states) (index : Nat) {facts : List ValueId}
    (bounded : EmptyFactsWithin limit facts) : EmptyStatesWithin limit (states.set! index (some facts)) := by
  intro other next lookup
  change (states.setIfInBounds index (some facts))[other]? = some (some next) at lookup
  rw [Array.getElem?_setIfInBounds] at lookup
  split at lookup
  · split at lookup
    · obtain ⟨rfl⟩ := Option.some.inj (Option.some.inj lookup)
      exact bounded
    · cases lookup
  · exact checked other next lookup

theorem emptyStateMeasure_discovers {limit : Nat} {states : Array (Option (List ValueId))}
    {index : Nat} (lookup : states[index]? = some none) {facts : List ValueId}
    (bounded : EmptyFactsWithin limit facts) :
    emptyStateMeasure limit (states.set! index (some facts)) < emptyStateMeasure limit states := by
  have equality := emptyStateMeasure_set (limit := limit) lookup facts
  have bound := bounded.length_le
  simp only [emptyStateWeight] at equality
  omega

theorem emptyStateMeasure_intersects {limit : Nat} {states : Array (Option (List ValueId))}
    {index : Nat} {facts : List ValueId} (lookup : states[index]? = some (some facts))
    (keep : ValueId → Bool) (changed : facts.filter keep ≠ facts) :
    emptyStateMeasure limit (states.set! index (some (facts.filter keep))) < emptyStateMeasure limit states := by
  have equality := emptyStateMeasure_set (limit := limit) lookup (facts.filter keep)
  have bound := filter_shortens_of_changed facts keep changed
  simp only [emptyStateWeight] at equality
  omega

theorem emptyFactRound_within (module : GIR.Module) (func : Func)
    (types : Array (Option VTy)) (provenance : ReplacementQueries) (states : Array (Option (List ValueId)))
    (checked : EmptyStatesWithin func.numValues states)
    (operands : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      ∀ value ∈ inst.uses, value < func.numValues)
    (parameters : ∀ block ∈ func.blocks.toList, ∀ param ∈ block.params, param.1 < func.numValues) :
    EmptyStatesWithin func.numValues (emptyFactRound module func types provenance states).1 := by
  unfold emptyFactRound
  change EmptyStatesWithin func.numValues ((forIn' (m := Id) [:func.blocks.size] (states, false) _).1)
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply list_forIn'_invariant (property := fun state : Array (Option (List ValueId)) × Bool =>
    EmptyStatesWithin func.numValues state.1)
  · exact checked
  · intro block member current valid
    dsimp only
    split
    · rename_i body found
      split
      · rename_i incoming present
        have blockMember := Array.mem_toList_iff.mpr (Array.mem_of_getElem? found)
        have incomingBounds := checked block incoming (Option.join_eq_some_iff.mp present)
        have outgoingBounds := emptyFactsWithin_transferEmptyBlock module types provenance incoming body
          incomingBounds (operands body blockMember)
        apply list_forIn_state_invariant (property := fun state : Array (Option (List ValueId)) × Bool =>
          EmptyStatesWithin func.numValues state.1)
        · exact valid
        · intro edge current valid
          obtain ⟨target, args⟩ := edge
          have edgeBounds := emptyFactsWithin_transferEmptyEdge func _ target args outgoingBounds parameters
          dsimp only
          split
          · split
            · exact valid.set _ edgeBounds
            · rename_i previous lookup
              split
              · exact valid.set _ ((valid target previous lookup).subset List.filter_sublist)
              · exact valid
            · exact valid
          · exact valid
      · exact valid
    · exact valid

structure EmptyRoundProgress (limit : Nat) (initial : Array (Option (List ValueId)))
    (current : Array (Option (List ValueId)) × Bool) : Prop where
  within : EmptyStatesWithin limit current.1
  measure : emptyStateMeasure limit current.1 ≤ emptyStateMeasure limit initial
  changed : current.2 = true → emptyStateMeasure limit current.1 < emptyStateMeasure limit initial
  unchanged : current.2 = false → current.1 = initial

theorem EmptyRoundProgress.update {limit : Nat} {initial : Array (Option (List ValueId))}
    {current : Array (Option (List ValueId)) × Bool} (checked : EmptyRoundProgress limit initial current)
    {next : Array (Option (List ValueId))} (within : EmptyStatesWithin limit next)
    (decreases : emptyStateMeasure limit next < emptyStateMeasure limit current.1) :
    EmptyRoundProgress limit initial (next, true) :=
  ⟨within, Nat.le_trans (Nat.le_of_lt decreases) checked.measure,
    fun _ => Nat.lt_of_lt_of_le decreases checked.measure, by simp⟩

theorem emptyFactRound_progress (module : GIR.Module) (func : Func)
    (types : Array (Option VTy)) (provenance : ReplacementQueries) (states : Array (Option (List ValueId)))
    (checked : EmptyStatesWithin func.numValues states)
    (operands : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      ∀ value ∈ inst.uses, value < func.numValues)
    (parameters : ∀ block ∈ func.blocks.toList, ∀ param ∈ block.params, param.1 < func.numValues) :
    EmptyRoundProgress func.numValues states (emptyFactRound module func types provenance states) := by
  unfold emptyFactRound
  change EmptyRoundProgress func.numValues states (forIn' (m := Id) [:func.blocks.size] (states, false) _)
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply list_forIn'_invariant (property := EmptyRoundProgress func.numValues states)
  · exact ⟨checked, Nat.le_refl _, by simp, fun _ => rfl⟩
  · intro block member current valid
    dsimp only
    split
    · rename_i body found
      split
      · rename_i incoming present
        have blockMember := Array.mem_toList_iff.mpr (Array.mem_of_getElem? found)
        have incomingBounds := checked block incoming (Option.join_eq_some_iff.mp present)
        have outgoingBounds := emptyFactsWithin_transferEmptyBlock module types provenance incoming body
          incomingBounds (operands body blockMember)
        apply list_forIn_state_invariant (property := EmptyRoundProgress func.numValues states)
        · exact valid
        · intro edge current valid
          obtain ⟨target, args⟩ := edge
          have edgeBounds := emptyFactsWithin_transferEmptyEdge func _ target args outgoingBounds parameters
          dsimp only
          split
          · split
            · rename_i lookup
              exact valid.update (valid.within.set _ edgeBounds) (emptyStateMeasure_discovers lookup edgeBounds)
            · rename_i previous lookup
              split
              · rename_i changed
                apply valid.update (valid.within.set _ ((valid.within target previous lookup).subset List.filter_sublist))
                apply emptyStateMeasure_intersects lookup
                simpa using changed
              · exact valid
            · exact valid
          · exact valid
      · exact valid
    · exact valid

private theorem map_sum_bound (weight : α → Nat) (items : List α) (limit : Nat)
    (bounded : ∀ item ∈ items, weight item ≤ limit) :
    (items.map weight).sum ≤ items.length * limit := by
  induction items with
  | nil => simp
  | cons first rest ih =>
    have firstBound := bounded first (by simp)
    have restBound := ih (by intro item member; exact bounded item (by simp [member]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem emptyStateMeasure_bound {limit : Nat} {states : Array (Option (List ValueId))}
    (checked : EmptyStatesWithin limit states) : emptyStateMeasure limit states ≤ states.size * (limit + 1) := by
  apply map_sum_bound
  intro cell member
  cases cell with
  | none => exact Nat.le_refl _
  | some facts =>
    obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    exact Nat.le_trans (checked index facts lookup).length_le (Nat.le_succ _)

theorem emptyFactsAtBlocks_eq_rounds (module : GIR.Module) (func : Func)
    (types : Array (Option VTy)) (provenance : ReplacementQueries) (nonempty : 0 < func.blocks.size) :
    emptyFactsAtBlocks module func types provenance =
      dataflowRounds (emptyFactRound module func types provenance)
        ((Array.replicate func.blocks.size none).set! 0 (some [])) true
        ((func.blocks.size + 1) * (func.numValues + 1) + 1) := by
  have present : func.blocks.isEmpty = false := by
    simp [Array.isEmpty, Nat.ne_of_gt nonempty]
  unfold emptyFactsAtBlocks
  simp only [present, Bool.not_false, ite_true]
  rfl

theorem emptyFactsAtBlocks_stable (module : GIR.Module) (func : Func)
    (types : Array (Option VTy)) (provenance : ReplacementQueries) (nonempty : 0 < func.blocks.size)
    (operands : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      ∀ value ∈ inst.uses, value < func.numValues)
    (parameters : ∀ block ∈ func.blocks.toList, ∀ param ∈ block.params, param.1 < func.numValues) :
    EmptyStatesWithin func.numValues (emptyFactsAtBlocks module func types provenance) ∧
      (emptyFactRound module func types provenance
        (emptyFactsAtBlocks module func types provenance)).1 = emptyFactsAtBlocks module func types provenance := by
  let seed : Array (Option (List ValueId)) := (Array.replicate func.blocks.size none).set! 0 (some [])
  have initial : EmptyStatesWithin func.numValues seed := by
    apply EmptyStatesWithin.set
    · intro index facts lookup
      simp only [Array.getElem?_replicate] at lookup
      split at lookup <;> cases lookup
    · exact ⟨by simp, by simp⟩
  have progress := fun states checked => emptyFactRound_progress module func types provenance states checked operands parameters
  have bound := emptyStateMeasure_bound initial
  have enough : emptyStateMeasure func.numValues seed <
      (func.blocks.size + 1) * (func.numValues + 1) + 1 := by
    have size : seed.size = func.blocks.size := by simp [seed]
    rw [size] at bound
    rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [emptyFactsAtBlocks_eq_rounds module func types provenance nonempty]
  constructor
  · apply dataflowRounds_invariant
    · intro states checked
      exact (progress states checked).within
    · exact initial
  · exact dataflowRounds_stable (property := EmptyStatesWithin func.numValues)
      (emptyFactRound module func types provenance) (emptyStateMeasure func.numValues)
      (fun states checked => ⟨(progress states checked).within, (progress states checked).changed⟩)
      (fun states checked => (progress states checked).unchanged)
      seed _ initial enough

end Goose.Lower.Validation

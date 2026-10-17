import Goose.Lower.Validation.ReplacementSource
import Goose.Lower.Validation.ShrinkFacts

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem rootsOverlap_false_of_disjoint {left right : List RootRef}
    (leftPresent : left ≠ []) (rightPresent : right ≠ [])
    (disjoint : DemandRootsDisjoint left right) : rootsOverlap left right = false := by
  have leftNotEmpty : left.isEmpty = false := List.isEmpty_eq_false_iff.mpr leftPresent
  have rightNotEmpty : right.isEmpty = false := List.isEmpty_eq_false_iff.mpr rightPresent
  simp only [rootsOverlap, leftNotEmpty, rightNotEmpty, Bool.false_or]
  apply List.any_eq_false.mpr
  intro root member overlapping
  obtain ⟨alias, aliasMember, overlaps⟩ := List.any_eq_true.mp overlapping
  simpa [disjoint root member alias aliasMember] using overlaps

def ReplacementApart (queries : ReplacementQueries) (owner : ValueId)
    (roots : ReplacementRootQuery) : Prop :=
  roots = some [] ∨ queries.value owner = some [] ∨
    ∃ left right, roots = some left ∧ queries.value owner = some right ∧
      DemandRootsDisjoint left right

theorem replacementOverlap_false_of_apart {queries : ReplacementQueries} {owner : ValueId}
    {roots : ReplacementRootQuery} (apart : ReplacementApart queries owner roots) :
    replacementOverlap roots (queries.value owner) = false := by
  rcases apart with empty | empty | ⟨left, right, rfl, equal, disjoint⟩
  · simp [empty, replacementOverlap]
  · cases roots with
    | none => simp [empty, replacementOverlap]
    | some roots => cases roots <;> simp [empty, replacementOverlap]
  · rw [equal]
    cases left with
    | nil => rfl
    | cons head tail =>
      cases right with
      | nil => rfl
      | cons other rest =>
        simp only [replacementOverlap]
        apply List.any_eq_false.mpr
        intro root member overlapping
        obtain ⟨alias, aliasMember, overlaps⟩ := List.any_eq_true.mp overlapping
        simpa [disjoint root member alias aliasMember] using overlaps

theorem killEmptyFacts_retains {facts : List ValueId} {roots : ReplacementRootQuery}
    {provenance : ReplacementQueries} {owner : ValueId} (present : owner ∈ facts)
    (apart : ReplacementApart provenance owner roots) :
    owner ∈ killEmptyFacts facts roots provenance := by
  simp only [killEmptyFacts, List.mem_filter]
  exact ⟨present, by simp [replacementOverlap_false_of_apart apart]⟩

theorem killEmptyFactSources_retains {facts operands : List ValueId}
    {types : Array (Option VTy)} {provenance : ReplacementQueries} {owner : ValueId}
    (present : owner ∈ facts)
    (apart : ∀ operand ∈ operands, valRefLike types operand = true →
      ReplacementApart provenance owner (provenance.value operand)) :
    owner ∈ killEmptyFactSources facts operands types provenance := by
  induction operands generalizing facts with
  | nil => exact present
  | cons operand rest ih =>
    apply ih
    · by_cases reference : valRefLike types operand = true
      · simpa only [reference, ite_true] using killEmptyFacts_retains present (apart operand (by simp) reference)
      · simpa [reference] using present
    · intro next member reference
      exact apart next (by simp [member]) reference

theorem transferEmptyInst_clear_has_owner (module : GIR.Module) (types : Array (Option VTy))
    (provenance : ReplacementQueries) (facts : List ValueId) (owner : ValueId) (origin : Option OriginId) :
    owner ∈ transferEmptyInst module types provenance facts (.eff (.clear owner origin)) := by
  simp only [transferEmptyInst, emptyFactSourceOperands, killEmptyFactSources, List.foldl_nil]
  split
  · rename_i present
    exact List.contains_iff_mem.mp present
  · exact List.mem_append_right _ (by simp)

end Goose.Lower.Validation

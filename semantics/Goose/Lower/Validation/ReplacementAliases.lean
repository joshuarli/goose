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

def ReplacementApart (provenance : Prov) (owner : ValueId) (roots : List RootRef) : Prop :=
  roots ≠ [] ∧ rootsAt provenance.vals owner ≠ [] ∧
    DemandRootsDisjoint roots (rootsAt provenance.vals owner)

theorem killEmptyFacts_retains {facts : List ValueId} {roots : List RootRef}
    {provenance : Prov} {owner : ValueId} (present : owner ∈ facts)
    (apart : ReplacementApart provenance owner roots) :
    owner ∈ killEmptyFacts facts roots provenance := by
  have rootsNotEmpty : roots.isEmpty = false := List.isEmpty_eq_false_iff.mpr apart.1
  have aliasesNotEmpty : (rootsAt provenance.vals owner).isEmpty = false :=
    List.isEmpty_eq_false_iff.mpr apart.2.1
  simp only [killEmptyFacts, rootsNotEmpty, Bool.false_eq_true, ite_false, List.mem_filter]
  exact ⟨present, by simp [aliasesNotEmpty, rootsOverlap_false_of_disjoint apart.1 apart.2.1 apart.2.2]⟩

theorem killEmptyFactSources_retains {facts operands : List ValueId}
    {types : Array (Option VTy)} {provenance : Prov} {owner : ValueId}
    (present : owner ∈ facts)
    (apart : ∀ operand ∈ operands, valRefLike types operand = true →
      ReplacementApart provenance owner (rootsAt provenance.vals operand)) :
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
    (provenance : Prov) (facts : List ValueId) (owner : ValueId) (origin : Option OriginId) :
    owner ∈ transferEmptyInst module types provenance facts (.eff (.clear owner origin)) := by
  simp only [transferEmptyInst, emptyFactSourceOperands, killEmptyFactSources, List.foldl_nil]
  split
  · rename_i present
    exact List.contains_iff_mem.mp present
  · exact List.mem_append_right _ (by simp)

end Goose.Lower.Validation

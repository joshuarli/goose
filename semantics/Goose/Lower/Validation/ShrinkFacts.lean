import Goose.Lower.Validation.ShrinkDataflow
import Goose.Lower.Validation.ReplacementSource

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def EmptyFactsWithin (limit : Nat) (facts : List ValueId) : Prop :=
  facts.Nodup ∧ ∀ value ∈ facts, value < limit

theorem EmptyFactsWithin.subset {limit : Nat} {before after : List ValueId}
    (checked : EmptyFactsWithin limit before) (subset : after.Sublist before) :
    EmptyFactsWithin limit after :=
  ⟨checked.1.sublist subset, fun value member => checked.2 value (subset.subset member)⟩

theorem killEmptyFacts_sublist (facts : List ValueId) (roots : List RootRef) (provenance : Prov) :
    (killEmptyFacts facts roots provenance).Sublist facts := by
  unfold killEmptyFacts
  split
  · exact List.nil_sublist _
  · exact List.filter_sublist

theorem killEmptyFactSources_sublist (facts operands : List ValueId)
    (types : Array (Option VTy)) (provenance : Prov) :
    (killEmptyFactSources facts operands types provenance).Sublist facts := by
  unfold killEmptyFactSources
  induction operands generalizing facts with
  | nil => exact .refl _
  | cons value rest ih =>
    simp only [List.foldl_cons]
    apply List.Sublist.trans (ih _)
    split
    · exact killEmptyFacts_sublist _ _ _
    · exact .refl _

theorem EmptyFactsWithin.clear {limit : Nat} {facts : List ValueId} (checked : EmptyFactsWithin limit facts)
    {owner : ValueId} (bounded : owner < limit) :
    EmptyFactsWithin limit (if facts.contains owner then facts else facts ++ [owner]) := by
  split
  · exact checked
  · rename_i absent
    have notMember : owner ∉ facts := by simpa using absent
    constructor
    · exact List.nodup_append.mpr ⟨checked.1, by simp, by
        intro value member other otherMember equal
        have same : other = owner := List.mem_singleton.mp otherMember
        subst other
        subst value
        exact notMember member⟩
    · intro value member
      rcases List.mem_append.mp member with previous | fresh
      · exact checked.2 value previous
      · simpa using (List.mem_singleton.mp fresh) ▸ bounded

theorem emptyFactsWithin_transferEmptyEdge (func : Func) (facts : List ValueId) (target : BlockId)
    (args : List ValueId) (checked : EmptyFactsWithin func.numValues facts)
    (parameters : ∀ block ∈ func.blocks.toList, ∀ param ∈ block.params, param.1 < func.numValues) :
    EmptyFactsWithin func.numValues (transferEmptyEdge func facts target args) := by
  unfold transferEmptyEdge
  cases lookup : func.blocks[target]? with
  | none => exact checked
  | some block =>
    apply List.foldlRecOn (motive := fun state => EmptyFactsWithin func.numValues state)
    · exact checked
    · intro state previous item member
      obtain ⟨⟨value, ty⟩, arg⟩ := item
      have bounded := parameters block (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))
        (value, ty) (List.of_mem_zip member).1
      dsimp only
      split
      · rename_i both
        have known : state.contains arg = true ∧ state.contains value = false := by simpa using both
        have absent := known.2
        have clear := previous.clear bounded
        simpa only [absent, Bool.false_eq_true, ite_false] using clear
      · exact previous

theorem transferEmptyInst_sublist (module : GIR.Module) (types : Array (Option VTy))
    (provenance : Prov) (facts : List ValueId) (inst : Inst)
    (uncleared : ∀ owner origin, inst ≠ .eff (.clear owner origin)) :
    (transferEmptyInst module types provenance facts inst).Sublist facts := by
  cases inst with
  | «def» result op =>
    cases op <;> dsimp only [transferEmptyInst]
    all_goals
      repeat' first
      | exact List.Sublist.refl _
      | exact List.nil_sublist _
      | exact killEmptyFacts_sublist _ _ _
      | exact killEmptyFactSources_sublist _ _ _ _
      | apply List.Sublist.trans (killEmptyFacts_sublist _ _ _)
      | apply List.Sublist.trans (killEmptyFactSources_sublist _ _ _ _)
      | split
  | eff effect =>
    cases effect <;> dsimp only [transferEmptyInst]
    all_goals
      repeat' first
      | exact List.Sublist.refl _
      | exact List.nil_sublist _
      | exact killEmptyFacts_sublist _ _ _
      | exact killEmptyFactSources_sublist _ _ _ _
      | apply List.Sublist.trans (killEmptyFacts_sublist _ _ _)
      | apply List.Sublist.trans (killEmptyFactSources_sublist _ _ _ _)
      | exact False.elim (uncleared _ _ rfl)
      | split
  | term term =>
    exact killEmptyFactSources_sublist _ _ _ _

theorem emptyFactsWithin_transferEmptyInst (module : GIR.Module) (types : Array (Option VTy))
    (provenance : Prov) (facts : List ValueId) (inst : Inst) {limit : Nat}
    (checked : EmptyFactsWithin limit facts) (bounded : ∀ value ∈ inst.uses, value < limit) :
    EmptyFactsWithin limit (transferEmptyInst module types provenance facts inst) := by
  by_cases clear : ∃ owner origin, inst = .eff (.clear owner origin)
  · obtain ⟨owner, origin, rfl⟩ := clear
    have ownerBound := bounded owner (by simp [Inst.uses, Effect.uses])
    change EmptyFactsWithin limit (if facts.contains owner then facts else facts ++ [owner])
    exact checked.clear ownerBound
  · exact checked.subset (transferEmptyInst_sublist module types provenance facts inst (by
      intro owner origin equal
      exact clear ⟨owner, origin, equal⟩))

theorem emptyFactsWithin_transferEmptyBlock (module : GIR.Module) (types : Array (Option VTy))
    (provenance : Prov) (facts : List ValueId) (block : GIR.Block) {limit : Nat}
    (checked : EmptyFactsWithin limit facts)
    (bounded : ∀ inst ∈ block.insts, ∀ value ∈ inst.uses, value < limit) :
    EmptyFactsWithin limit (transferEmptyBlock module types provenance facts block) := by
  unfold transferEmptyBlock
  apply List.foldlRecOn
  · exact checked
  · intro current valid inst member
    exact emptyFactsWithin_transferEmptyInst module types provenance current inst valid (bounded inst member)

theorem EmptyFactsWithin.length_le {limit : Nat} {facts : List ValueId}
    (checked : EmptyFactsWithin limit facts) : facts.length ≤ limit := by
  have subset : facts ⊆ List.range limit := by
    intro value member
    exact List.mem_range.mpr (checked.2 value member)
  simpa using checked.1.length_le_of_subset subset

theorem filter_shortens_of_changed (facts : List ValueId) (keep : ValueId → Bool)
    (changed : facts.filter keep ≠ facts) : (facts.filter keep).length < facts.length := by
  have subset : (facts.filter keep).Sublist facts := List.filter_sublist
  apply Nat.lt_of_le_of_ne subset.length_le
  intro same
  exact changed (subset.eq_of_length_le (Nat.le_of_eq same.symm))

end Goose.Lower.Validation

import Goose.Lower.Validation.ReplacementProvenance
import Goose.Core.Sound.Invert

namespace Goose.Lower.Validation.ProvenanceConvergence

open Goose.Core Goose.Core.Sound Goose.GIR

def tableWeight (table : Array (List RootRef)) : Nat :=
  (table.toList.map List.length).sum

def weight (provenance : Prov) : Nat := tableWeight provenance.slots + tableWeight provenance.vals

def TableBound (rootUniverse : List RootRef) (table : Array (List RootRef)) : Prop :=
  ∀ cell, (rootsAt table cell).Nodup ∧ rootsAt table cell ⊆ rootUniverse

def Bounded (rootUniverse : List RootRef) (provenance : Prov) : Prop :=
  TableBound rootUniverse provenance.slots ∧ TableBound rootUniverse provenance.vals

theorem unionRoots_nodup {left right : List RootRef} (nodup : left.Nodup) :
    (unionRoots left right).Nodup := by
  unfold unionRoots
  apply List.foldlRecOn (motive := List.Nodup) right _ nodup
  intro roots prior root _
  split
  · exact prior
  · rename_i absent
    apply List.nodup_append.mpr
    refine ⟨prior, by simp, ?_⟩
    intro a member b atRoot same
    have equal : b = root := by simpa only [List.mem_singleton] using atRoot
    subst b
    subst a
    exact absent (List.contains_iff_mem.mpr member)

theorem unionRoots_subset {left right rootUniverse : List RootRef}
    (leftBound : left ⊆ rootUniverse) (rightBound : right ⊆ rootUniverse) :
    unionRoots left right ⊆ rootUniverse := by
  intro root member
  exact (unionRoots_mem _ _ _ member).elim (fun h => leftBound h) (fun h => rightBound h)

private theorem listWeight_set {rows : List (List RootRef)} {index : Nat}
    (bounded : index < rows.length) (roots : List RootRef) :
    ((rows.set index roots).map List.length).sum + rows[index].length =
      (rows.map List.length).sum + roots.length := by
  induction rows generalizing index with
  | nil => simp at bounded
  | cons first rest ih =>
    cases index with
    | zero =>
      simp only [List.set, List.map_cons, List.sum_cons, List.getElem_cons_zero]
      omega
    | succ index =>
      have next : index < rest.length := by simpa using bounded
      have prior := ih next
      simp only [List.set, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      omega

theorem tableWeight_set {table : Array (List RootRef)} {index : Nat}
    (bounded : index < table.size) (roots : List RootRef) :
    tableWeight (table.set! index roots) + (rootsAt table index).length =
      tableWeight table + roots.length := by
  unfold tableWeight
  simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  have next : index < table.toList.length := by simpa using bounded
  have row : rootsAt table index = table.toList[index] := by
    simp only [rootsAt, Array.getElem?_eq_getElem bounded, Option.getD_some, Array.getElem_toList]
  rw [row]
  exact listWeight_set next roots

theorem addTo_weight (table : Array (List RootRef)) (index : Nat) (roots : List RootRef) :
    tableWeight table ≤ tableWeight (GIR.addTo table index roots).1 ∧
      ((GIR.addTo table index roots).2 = true → tableWeight table < tableWeight (GIR.addTo table index roots).1) ∧
      ((GIR.addTo table index roots).2 = false → (GIR.addTo table index roots).1 = table) := by
  unfold GIR.addTo
  dsimp only
  split
  · exact ⟨Nat.le_refl _, by simp, fun _ => rfl⟩
  · rename_i changed
    have bounded : index < table.size := by
      have : ¬ index ≥ table.size := by
        intro outside
        exact changed (by simp [outside])
      omega
    have notEqual : (unionRoots (rootsAt table index) roots).length ≠ (rootsAt table index).length := by
      intro equal
      exact changed (by simp [equal])
    have oldLe := (unionRoots_contains_prior (rootsAt table index) roots).length_le
    have increased : (rootsAt table index).length < (unionRoots (rootsAt table index) roots).length := by omega
    have balance := tableWeight_set bounded (unionRoots (rootsAt table index) roots)
    dsimp only
    exact ⟨by omega, fun _ => by omega, by simp⟩

theorem TableBound.set {rootUniverse : List RootRef} {table : Array (List RootRef)}
    (bound : TableBound rootUniverse table) (index : Nat) {roots : List RootRef}
    (nodup : roots.Nodup) (subset : roots ⊆ rootUniverse) :
    TableBound rootUniverse (table.set! index roots) := by
  intro cell
  simp only [rootsAt, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  split
  · split
    · exact ⟨nodup, subset⟩
    · exact ⟨by simp, by simp⟩
  · exact bound cell

theorem TableBound.addTo {rootUniverse : List RootRef} {table : Array (List RootRef)}
    (bound : TableBound rootUniverse table) (index : Nat) {roots : List RootRef}
    (subset : roots ⊆ rootUniverse) : TableBound rootUniverse (GIR.addTo table index roots).1 := by
  unfold GIR.addTo
  dsimp only
  split
  · exact bound
  · exact bound.set index (unionRoots_nodup (bound index).1)
      (unionRoots_subset (bound index).2 subset)

private theorem listWeight_le {rootUniverse : List RootRef} {rows : List (List RootRef)}
    (bound : ∀ row ∈ rows, row.Nodup ∧ row ⊆ rootUniverse) :
    (rows.map List.length).sum ≤ rows.length * rootUniverse.length := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
    have first := (bound row (by simp)).1.length_le_of_subset (bound row (by simp)).2
    have tail := ih (fun row member => bound row (by simp [member]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem TableBound.weight_le {rootUniverse : List RootRef} {table : Array (List RootRef)}
    (bound : TableBound rootUniverse table) : tableWeight table ≤ table.size * rootUniverse.length := by
  have each : ∀ row ∈ table.toList, row.Nodup ∧ row ⊆ rootUniverse := by
    intro row member
    obtain ⟨cell, atRow⟩ := List.mem_iff_getElem?.mp member
    have same : rootsAt table cell = row := by
      simp only [rootsAt, ← Array.getElem?_toList, atRow, Option.getD_some]
    simpa only [same] using bound cell
  simpa only [tableWeight, Array.length_toList] using listWeight_le each

theorem Bounded.weight_le {rootUniverse : List RootRef} {provenance : Prov}
    (bound : Bounded rootUniverse provenance) :
    weight provenance ≤ (provenance.slots.size + provenance.vals.size) * rootUniverse.length := by
  have slots := bound.1.weight_le
  have vals := bound.2.weight_le
  simp only [weight, Nat.add_mul]
  omega

structure Growth (before after : Prov × Bool) : Prop where
  slots : after.1.slots.size = before.1.slots.size
  vals : after.1.vals.size = before.1.vals.size
  nondecreasing : weight before.1 ≤ weight after.1
  changed : before.2 = true → after.2 = true
  strict : before.2 = false → after.2 = true → weight before.1 < weight after.1
  quiet : after.2 = false → after.1 = before.1

theorem Growth.refl (state : Prov × Bool) : Growth state state := by
  refine ⟨rfl, rfl, Nat.le_refl _, id, ?_, fun _ => rfl⟩
  intro quiet changed
  simp_all

theorem Growth.trans {before middle after : Prov × Bool}
    (first : Growth before middle) (second : Growth middle after) : Growth before after := by
  refine ⟨second.slots.trans first.slots, second.vals.trans first.vals,
    Nat.le_trans first.nondecreasing second.nondecreasing, fun h => second.changed (first.changed h), ?_, ?_⟩
  · intro quiet changed
    cases middleFlag : middle.2 with
    | false => exact Nat.lt_of_le_of_lt first.nondecreasing (second.strict middleFlag changed)
    | true => exact Nat.lt_of_lt_of_le (first.strict quiet middleFlag) second.nondecreasing
  · intro quiet
    have middleQuiet : middle.2 = false := by
      cases flag : middle.2 with
      | false => rfl
      | true => have := second.changed flag; simp_all
    exact (second.quiet quiet).trans (first.quiet middleQuiet)

theorem Growth.addValues (state : Prov × Bool) (index : Nat) (roots : List RootRef) :
    Growth state
      ({ state.1 with vals := (GIR.addTo state.1.vals index roots).1 },
        state.2 || (GIR.addTo state.1.vals index roots).2) := by
  obtain ⟨nondecreasing, strict, quiet⟩ := addTo_weight state.1.vals index roots
  refine ⟨rfl, addTo_size _ _ _, ?_, ?_, ?_, ?_⟩
  · dsimp only [weight]
    omega
  · intro changed
    simp [changed]
  · intro prior changed
    have inserted : (GIR.addTo state.1.vals index roots).2 = true := by simpa [prior] using changed
    have := strict inserted
    dsimp only [weight]
    omega
  · intro unchanged
    have inserted : (GIR.addTo state.1.vals index roots).2 = false := by simpa using (Bool.or_eq_false_iff.mp unchanged).2
    rw [quiet inserted]

theorem Growth.addSlots (state : Prov × Bool) (index : Nat) (roots : List RootRef) :
    Growth state
      ({ state.1 with slots := (GIR.addTo state.1.slots index roots).1 },
        state.2 || (GIR.addTo state.1.slots index roots).2) := by
  obtain ⟨nondecreasing, strict, quiet⟩ := addTo_weight state.1.slots index roots
  refine ⟨addTo_size _ _ _, rfl, ?_, ?_, ?_, ?_⟩
  · dsimp only [weight]
    omega
  · intro changed
    simp [changed]
  · intro prior changed
    have inserted : (GIR.addTo state.1.slots index roots).2 = true := by simpa [prior] using changed
    have := strict inserted
    dsimp only [weight]
    omega
  · intro unchanged
    have inserted : (GIR.addTo state.1.slots index roots).2 = false := by simpa using (Bool.or_eq_false_iff.mp unchanged).2
    rw [quiet inserted]

end Goose.Lower.Validation.ProvenanceConvergence

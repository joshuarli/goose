import Goose.Lower.Validation.ReplacementProvenance

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.Core.Sound Goose.GIR

theorem canonical_start_value_floor (results : Array (List RootRef))
    (types : Array (Option VTy)) (func : Func) (rootCount : Nat) (value : ValueId)
    (root : RootRef) (seed : root ∈ rootsAt (provStart types func).vals value) :
    root ∈ rootsAt (func.provenance results types rootCount).vals value :=
  (provFix_extends results types func _ (provStart types func)).2.2.2 value root seed

theorem canonical_slot_seed_floor (results : Array (List RootRef))
    (types : Array (Option VTy)) (func : Func) (rootCount : Nat) (slot : SlotId)
    (root : RootRef) (seed : root ∈ rootsAt func.slotRootSeeds slot) :
    root ∈ rootsAt (func.provenance results types rootCount).slots slot :=
  (provFix_extends results types func _ (provStart types func)).2.2.1 slot root seed

private theorem seed_rows_contains (index : Nat) (root : RootRef) (rows : List (Nat × List RootRef))
    (initial : List RootRef) (present : root ∈ initial ∨ ∃ row ∈ rows, row.1 = index ∧ root ∈ row.2) :
    root ∈ rows.foldl (fun roots row => if row.1 == index then unionRoots roots row.2 else roots) initial := by
  induction rows generalizing initial with
  | nil => simpa using present
  | cons row rest ih =>
      apply ih
      rcases present with prior | ⟨selected, member, same, included⟩
      · left
        dsimp only
        split
        · exact unionRoots_left _ _ _ prior
        · exact prior
      · rcases List.mem_cons.mp member with equal | later
        · subst selected
          left
          simp only [same, beq_self_eq_true, ite_true]
          exact unionRoots_right _ _ _ included
        · exact Or.inr ⟨selected, later, same, included⟩

theorem valueRootSeeds_contains {func : Func} {value : ValueId} {declared : List RootRef}
    (bounded : value < func.numValues) (row : (value, declared) ∈ func.roots.values.getD #[]) :
    ∀ root ∈ declared, root ∈ rootsAt func.valueRootSeeds value := by
  intro root included
  have present : (Array.replicate func.numValues ([] : List RootRef))[value]? = some [] := by
    simp [bounded]
  simp only [rootsAt, Func.valueRootSeeds, Array.getElem?_mapIdx, present,
    Option.map_some, Option.getD_some]
  rw [← Array.foldl_toList]
  exact seed_rows_contains value root _ []
    (Or.inr ⟨(value, declared), Array.mem_toList_iff.mpr row, rfl, included⟩)

private theorem entry_set_retains {table : Array (List RootRef)} {value cell : Nat}
    (inside : value < table.size) (root : RootRef) (prior : root ∈ rootsAt table cell)
    (added : List RootRef) :
    root ∈ rootsAt (table.set! value (unionRoots (rootsAt table value) added)) cell := by
  by_cases same : value = cell
  · subst cell
    simp only [rootsAt, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_self_of_lt inside, Option.getD_some]
    exact unionRoots_left _ _ _ prior
  · simpa only [rootsAt, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne same] using prior

theorem provStart_value_seed_floor (types : Array (Option VTy)) (func : Func)
    (value : ValueId) (root : RootRef) (seed : root ∈ rootsAt func.valueRootSeeds value) :
    root ∈ rootsAt (provStart types func).vals value := by
  unfold provStart
  cases entry : func.blocks[0]? with
  | none => exact seed
  | some block =>
      simp only
      apply List.foldlRecOn
        (motive := fun table : Array (List RootRef) => root ∈ rootsAt table value)
        block.params.zipIdx _ seed
      intro table prior pair member
      try dsimp only
      split
      · rename_i allowed
        have inside : pair.1.1 < table.size := by simpa using (Bool.and_eq_true_iff.mp allowed).2
        exact entry_set_retains inside root prior _
      · exact prior

theorem canonical_value_metadata_floor (results : Array (List RootRef))
    (types : Array (Option VTy)) (func : Func) (rootCount : Nat)
    {value : ValueId} {declared : List RootRef} (bounded : value < func.numValues)
    (row : (value, declared) ∈ func.roots.values.getD #[]) :
    ∀ root ∈ declared, root ∈ rootsAt (func.provenance results types rootCount).vals value := by
  intro root included
  exact canonical_start_value_floor results types func rootCount value root
    (provStart_value_seed_floor types func value root (valueRootSeeds_contains bounded row root included))

end Goose.Lower.Validation.SourceCanonicalRootFloors

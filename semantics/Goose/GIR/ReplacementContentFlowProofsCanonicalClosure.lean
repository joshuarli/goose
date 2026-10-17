import Goose.GIR.ReplacementContentFlowProofsCanonicalMemory
import Goose.GIR.AdmittedRegionsSound

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

private theorem contentFold_absent (rows : List (Nat × List RootRef)) (index : Nat)
    (absent : ∀ row ∈ rows, row.1 ≠ index) (initial : List RootRef) :
    rows.foldl (fun roots row => if row.1 == index then row.2 else roots) initial = initial := by
  induction rows generalizing initial with
  | nil => rfl
  | cons row rows ih =>
      have different := absent row (by simp)
      simpa [different] using ih (fun selected member => absent selected (by simp [member])) initial

private theorem contentFold_unique (rows : List (Nat × List RootRef)) (index : Nat)
    (unique : (rows.map Prod.fst).Nodup) (initial : List RootRef) :
    rows.foldl (fun roots row => if row.1 == index then row.2 else roots) initial =
      ((rows.find? (·.1 == index)).map Prod.snd).getD initial := by
  induction rows generalizing initial with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.map_cons,List.nodup_cons] at unique
      by_cases same : row.1 = index
      · have absent : ∀ selected ∈ rows, selected.1 ≠ index := by
          intro selected member equal
          apply unique.1
          exact List.mem_map.mpr ⟨selected,member,equal.trans same.symm⟩
        simpa [same] using contentFold_absent rows index absent row.2
      · simpa [same] using ih unique.2 initial

theorem contentRoots_find {func : Func}
    (unique : (func.roots.contents.toList.map Prod.fst).Nodup) (index : Nat) :
    func.contentRoots index = ((func.roots.contents.find? (·.1 == index)).map Prod.snd).getD [] := by
  simpa only [Func.contentRoots,← Array.foldl_toList,← Array.find?_toList] using
    contentFold_unique func.roots.contents.toList index unique []

theorem unionRoots_prior_sublist (before added : List RootRef) :
    before.Sublist (unionRoots before added) := by
  unfold unionRoots
  apply List.foldlRecOn (motive := fun current => before.Sublist current) added _
    (List.Sublist.refl before)
  intro current prior root _
  split
  · exact prior
  · exact prior.trans (List.sublist_append_left _ _)

theorem addTo_quiet_contains {table : Array (List RootRef)} {index : Nat} {roots : List RootRef}
    (bounded : index < table.size) (quiet : (Goose.GIR.addTo table index roots).2 = false) :
    roots ⊆ rootsAt table index := by
  have equalLength : (unionRoots (rootsAt table index) roots).length =
      (rootsAt table index).length := by
    unfold Goose.GIR.addTo at quiet
    dsimp only at quiet
    split at quiet
    · rename_i condition
      simpa [Nat.not_le.mpr bounded] using condition
    · contradiction
  have equal := (unionRoots_prior_sublist (rootsAt table index) roots).eq_of_length_le
    (Nat.le_of_eq equalLength)
  intro root member
  rw [equal]
  exact (unionRoots_mem_iff _ _ _).mpr (Or.inr member)

theorem addTo_contains {table : Array (List RootRef)} {index : Nat} {roots : List RootRef}
    (bounded : index < table.size) :
    roots ⊆ rootsAt (Goose.GIR.addTo table index roots).1 index := by
  unfold Goose.GIR.addTo
  dsimp only
  split
  · rename_i condition
    exact addTo_quiet_contains bounded (by simp [Goose.GIR.addTo, condition])
  · simp only [rootsAt, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self,
      bounded, ite_true, Option.getD_some]
    intro root member
    exact (unionRoots_mem_iff _ _ _).mpr (Or.inr member)

def RootTableGrowth (before after : Array (List RootRef)) : Prop :=
  ∀ index, rootsAt before index ⊆ rootsAt after index

theorem RootTableGrowth.refl (table : Array (List RootRef)) : RootTableGrowth table table :=
  fun _ _ member => member

theorem RootTableGrowth.trans {before middle after : Array (List RootRef)}
    (first : RootTableGrowth before middle) (second : RootTableGrowth middle after) :
    RootTableGrowth before after := fun index _ member => second index (first index member)

theorem addTo_growth (table : Array (List RootRef)) (index : Nat) (roots : List RootRef) :
    RootTableGrowth table (Goose.GIR.addTo table index roots).1 := by
  unfold Goose.GIR.addTo
  dsimp only
  split
  · exact .refl _
  · intro cell root member
    by_cases same : index = cell
    · subst cell
      by_cases bounded : index < table.size
      · simp only [rootsAt, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self,
          bounded, ite_true, Option.getD_some]
        exact (unionRoots_mem_iff _ _ _).mpr (Or.inl member)
      · simpa [rootsAt, bounded] using member
    · simpa [rootsAt, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, same] using member

theorem provStep_def_roots {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {value : ValueId} {op : Op}
    (bounded : value < provenance.vals.size)
    (quiet : func.provStep results vt (provenance,false) (.def value op) = (provenance,false)) :
    rootsOfDef results vt func provenance value op ⊆ rootsAt provenance.vals value := by
  have flags := congrArg Prod.snd quiet
  exact addTo_quiet_contains bounded (by simpa [Func.provStep] using flags)

theorem provStep_slotInit_roots {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {slot : SlotId} {value : ValueId} {origin : Option OriginId}
    (bounded : slot < provenance.slots.size)
    (quiet : func.provStep results vt (provenance,false) (.eff (.slotInit slot value origin)) =
      (provenance,false)) :
    rootsAt provenance.vals value ⊆ rootsAt provenance.slots slot := by
  have flags := congrArg Prod.snd quiet
  exact addTo_quiet_contains bounded (by simpa [Func.provStep] using flags)

private def storeRoot (value : ValueId) (state : Prov × Bool) (root : RootRef) : Prov × Bool :=
  match root with
  | .local slot =>
      let (slots,changed) := Goose.GIR.addTo state.1.slots slot (rootsAt state.1.vals value)
      ({ state.1 with slots },state.2 || changed)
  | _ => state

private theorem storeRoot_values (value : ValueId) (state : Prov × Bool) (root : RootRef) :
    (storeRoot value state root).1.vals = state.1.vals := by
  cases root <;> rfl

private theorem storeRoot_growth (value : ValueId) (state : Prov × Bool) (root : RootRef) :
    RootTableGrowth state.1.slots (storeRoot value state root).1.slots := by
  cases root with
  | «local» slot => exact addTo_growth _ _ _
  | _ => exact .refl _

private theorem storeFold_values (value : ValueId) (state : Prov × Bool) (roots : List RootRef) :
    (roots.foldl (storeRoot value) state).1.vals = state.1.vals := by
  apply List.foldlRecOn (motive := fun current : Prov × Bool => current.1.vals = state.1.vals)
    roots _ rfl
  intro current prior root _
  exact (storeRoot_values _ _ _).trans prior

private theorem storeFold_growth (value : ValueId) (state : Prov × Bool) (roots : List RootRef) :
    RootTableGrowth state.1.slots (roots.foldl (storeRoot value) state).1.slots := by
  apply List.foldlRecOn (motive := fun current : Prov × Bool => RootTableGrowth state.1.slots current.1.slots)
    roots _ (RootTableGrowth.refl _)
  intro current prior root _
  exact prior.trans (storeRoot_growth _ _ _)

private theorem storeFold_size (value : ValueId) (state : Prov × Bool) (roots : List RootRef) :
    (roots.foldl (storeRoot value) state).1.slots.size = state.1.slots.size := by
  apply List.foldlRecOn (motive := fun current : Prov × Bool => current.1.slots.size = state.1.slots.size)
    roots _ rfl
  intro current prior root _
  cases root with
  | «local» slot =>
      simp only [storeRoot, Goose.GIR.addTo]
      split <;> simpa using prior
  | _ => exact prior

theorem provStep_store_roots {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {address value : ValueId} {origin : Option OriginId}
    {slot : SlotId} (bounded : slot < provenance.slots.size)
    (target : RootRef.local slot ∈ rootsAt provenance.vals address)
    (quiet : func.provStep results vt (provenance,false) (.eff (.store address value origin)) =
      (provenance,false)) :
    rootsAt provenance.vals value ⊆ rootsAt provenance.slots slot := by
  obtain ⟨before,after,split⟩ := List.mem_iff_append.mp target
  have equation : func.provStep results vt (provenance,false) (.eff (.store address value origin)) =
      ((rootsAt provenance.vals address).foldl (storeRoot value) (provenance,false)) := rfl
  rw [equation, split, List.foldl_append, List.foldl_cons] at quiet
  let middle := before.foldl (storeRoot value) (provenance,false)
  have sizes : middle.1.slots.size = provenance.slots.size := storeFold_size _ _ _
  have values : middle.1.vals = provenance.vals := storeFold_values _ _ _
  have added := addTo_contains (table := middle.1.slots) (index := slot) (roots := rootsAt middle.1.vals value) (by rw [sizes]; exact bounded : slot < middle.1.slots.size)
  have continued := storeFold_growth value (storeRoot value middle (.local slot)) after
  have finalSlots := congrArg (fun pair : Prov × Bool => pair.1.slots) quiet
  rw [finalSlots] at continued
  intro root member
  apply continued slot
  apply added
  simpa [values] using member

#print axioms provStep_def_roots
#print axioms provStep_slotInit_roots
#print axioms provStep_store_roots

end Goose.GIR.ReplacementContentFlow.Model

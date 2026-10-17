import Goose.GIR.ReplacementContentFlowProofsCanonicalTransfer

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem start_canonicalMemory (func : Func) (vt : Array (Option VTy)) (provenance : Prov)
    (unique : (func.roots.contents.toList.map Prod.fst).Nodup) :
    (start func vt).CanonicalMemory func provenance := by
  rw [start_components]
  constructor
  · intro index bounded
    have bound : index < func.slots.size := by simpa using bounded
    simp only [flowAt,Array.getElem?_replicate,bound,ite_true,Option.getD_some]
    exact .pending _ _
  · intro index bounded observed
    have bound : index < func.params.length := by simpa using bounded
    have parameter : func.params.toArray[index]? = some func.params[index] := by simp [bound]
    change SymbolicRootsRefine func
      (flowAt (func.params.toArray.mapIdx fun index type =>
        if type.isRefSlice then .known [.contents index] else .known []) index) _
    simp only [flowAt,Array.getElem?_mapIdx,parameter,Option.map_some,Option.getD_some]
    split
    · obtain ⟨row,annotation⟩ := Option.isSome_iff_exists.mp observed
      have selection := Array.find?_some annotation
      have identity : row.1 = index := by simpa only [beq_iff_eq] using selection
      rcases row with ⟨selected,roots⟩
      change selected = index at identity
      subst selected
      have exactCeiling : func.contentRoots index = roots := by
        rw [contentRoots_find unique index,annotation]
        rfl
      rw [exactCeiling]
      exact .contents annotation
    · exact .known_empty _ _
  · intro index bounded
    have bound : index < func.params.length := by simpa using bounded
    simp [Write.SymbolicRefine,Array.getElem?_replicate,bound]

theorem SymbolicCells.set {func : Func} {upper : Nat → List RootRef}
    {cells : Array Roots} {index : Nat} {roots : Roots}
    (before : SymbolicCells func upper cells)
    (added : SymbolicRootsRefine func roots (upper index)) :
    SymbolicCells func upper (cells.set! index roots) := by
  intro cell bounded
  have originalBound : cell < cells.size := by simpa using bounded
  change SymbolicRootsRefine func ((cells.set! index roots)[cell]?.getD .unknown) _
  simp only [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds]
  by_cases same : index = cell
  · subst cell
    simpa [originalBound] using added
  · simpa [same,flowAt] using before cell originalBound

theorem start_canonicalValues (func : Func) (vt : Array (Option VTy)) (provenance : Prov)
    (seeds : ∀ entry : Block, func.blocks[0]? = some entry →
      ∀ pair index, (pair,index) ∈ entry.params.zipIdx → valRefLike vt pair.1 = true →
        RootRef.param index ∈ rootsAt provenance.vals pair.1) :
    SymbolicCells func (rootsAt provenance.vals) (start func vt).values := by
  cases found : func.blocks[0]? with
  | none =>
      intro index bounded
      have bound : index < func.numValues := by simpa [start,found] using bounded
      have cell : flowAt (start func vt).values index = .pending := by
        simp [start,found,flowAt,bound]
      rw [cell]
      exact .pending _ _
  | some entry =>
      rw [start_values_fold vt found]
      have base : SymbolicCells func (rootsAt provenance.vals) (Array.replicate func.numValues .pending) := by
        intro index bounded
        have bound : index < func.numValues := by simpa using bounded
        simp only [flowAt,Array.getElem?_replicate,bound,ite_true,Option.getD_some]
        exact .pending _ _
      apply List.foldlRecOn (motive := fun (values : Array Roots) => SymbolicCells func (rootsAt provenance.vals) values)
        entry.params.zipIdx _ base
      intro values before pair member
      apply before.set
      split
      · rename_i reference
        exact (SymbolicRootsRefine.parameter_iff func pair.2 _).mpr
          (Or.inl (seeds entry found pair.1 pair.2 member reference))
      · exact .known_empty _ _

#print axioms start_canonicalMemory
#print axioms start_canonicalValues

end Goose.GIR.ReplacementContentFlow.Model

import Goose.GIR.ReplacementContentFlowProofsCanonicalStart

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def HolderValues (func : Func) (vt : Array (Option VTy)) (provenance : Prov)
    (values : Array Roots) : Prop :=
  ∀ value, value < values.size → ∀ mutability payload,
    vt[value]? = some (some (.data (.ref mutability payload))) → payload.isRefLike = true →
      HolderRoots func payload (rootsAt provenance.vals value) (flowAt values value)

def HolderSlots (func : Func) (provenance : Prov) (values : Array Roots) : Prop :=
  ∀ slot storage, func.slots[slot]? = some storage → slot < values.size → ∀ mutability payload,
    storage.ty = .ref mutability payload → payload.isRefLike = true →
      HolderRoots func payload (rootsAt provenance.slots slot) (flowAt values slot)

structure State.CanonicalWithin (func : Func) (vt : Array (Option VTy)) (provenance : Prov)
    (state : State) : Prop where
  shape : state.Shape func
  values : SymbolicCells func (rootsAt provenance.vals) state.values
  memory : state.CanonicalMemory func provenance
  holderValues : HolderValues func vt provenance state.values
  holderSlots : HolderSlots func provenance state.slots

theorem HolderValues.set {func : Func} {vt : Array (Option VTy)} {provenance : Prov}
    {values : Array Roots} {index : Nat} {roots : Roots}
    (before : HolderValues func vt provenance values)
    (added : ∀ mutability payload, vt[index]? = some (some (.data (.ref mutability payload))) →
      payload.isRefLike = true → HolderRoots func payload (rootsAt provenance.vals index) roots) :
    HolderValues func vt provenance (values.set! index roots) := by
  intro value bounded mutability payload type reference
  have priorBound : value < values.size := by simpa using bounded
  change HolderRoots func payload _ ((values.set! index roots)[value]?.getD .unknown)
  simp only [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds]
  by_cases same : index = value
  · subst value
    simpa [priorBound] using added mutability payload type reference
  · simpa [same,flowAt] using before value priorBound mutability payload type reference

theorem start_holderSlots (func : Func) (vt : Array (Option VTy)) (provenance : Prov) :
    HolderSlots func provenance (start func vt).slots := by
  rw [start_components]
  intro slot storage _ bounded mutability payload _ _
  have bound : slot < func.slots.size := by simpa using bounded
  simp [HolderRoots,Roots.AtomsWithin,flowAt,bound]

theorem start_holderValues (func : Func) (vt : Array (Option VTy)) (provenance : Prov)
    (parameters : ∀ entry : Block, func.blocks[0]? = some entry →
      ∀ pair index, (pair,index) ∈ entry.params.zipIdx →
        ∃ type, pair.2 = .data type ∧ vt[pair.1]? = some (some (.data type)) ∧
          func.params[index]? = some type)
    (seeds : ∀ entry : Block, func.blocks[0]? = some entry →
      ∀ pair index, (pair,index) ∈ entry.params.zipIdx → valRefLike vt pair.1 = true →
        RootRef.param index ∈ rootsAt provenance.vals pair.1) :
    HolderValues func vt provenance (start func vt).values := by
  cases found : func.blocks[0]? with
  | none =>
      intro value bounded mutability payload type reference
      have bound : value < func.numValues := by simpa [start,found] using bounded
      simp [start,found,HolderRoots,Roots.AtomsWithin,flowAt,bound]
  | some entry =>
      rw [start_values_fold vt found]
      have base : HolderValues func vt provenance (Array.replicate func.numValues .pending) := by
        intro value bounded mutability payload type reference
        have bound : value < func.numValues := by simpa using bounded
        simp [HolderRoots,Roots.AtomsWithin,flowAt,bound]
      apply List.foldlRecOn (motive := fun values : Array Roots => HolderValues func vt provenance values)
        entry.params.zipIdx _ base
      intro values before pair member
      apply before.set
      intro mutability payload type reference
      obtain ⟨declared,_,canonical,formal⟩ := parameters entry found pair.1 pair.2 member
      have identical : declared = .ref mutability payload := by
        rw [canonical] at type
        exact VTy.data.inj (Option.some.inj (Option.some.inj type))
      subst declared
      have like : valRefLike vt pair.1.1 = true := by
        simp [valRefLike,canonical,VTy.refLike,Ty.isRefLike]
      simp only [like,ite_true]
      intro atom included
      have identical : atom = .param pair.2 := by simpa using included
      subst atom
      exact .parameter pair.2 mutability formal (seeds entry found pair.1 pair.2 member like)

theorem start_canonicalWithin (func : Func) (vt : Array (Option VTy)) (provenance : Prov)
    (unique : (func.roots.contents.toList.map Prod.fst).Nodup)
    (parameters : ∀ entry : Block, func.blocks[0]? = some entry →
      ∀ pair index, (pair,index) ∈ entry.params.zipIdx →
        ∃ type, pair.2 = .data type ∧ vt[pair.1]? = some (some (.data type)) ∧
          func.params[index]? = some type)
    (seeds : ∀ entry : Block, func.blocks[0]? = some entry →
      ∀ pair index, (pair,index) ∈ entry.params.zipIdx → valRefLike vt pair.1 = true →
        RootRef.param index ∈ rootsAt provenance.vals pair.1) :
    (start func vt).CanonicalWithin func vt provenance :=
  ⟨start_shape _ _,start_canonicalValues _ _ _ seeds,start_canonicalMemory _ _ _ unique,
    start_holderValues _ _ _ parameters seeds,start_holderSlots _ _ _⟩

theorem State.Extends.canonicalWithin {func : Func} {vt : Array (Option VTy)} {provenance : Prov}
    {before after : State} (growth : before.Extends after)
    (bounded : after.CanonicalWithin func vt provenance) : before.CanonicalWithin func vt provenance := by
  constructor
  · exact ⟨growth.values.size.trans bounded.shape.values,growth.slots.size.trans bounded.shape.slots,
      growth.contents.size.trans bounded.shape.contents,growth.writes.size.trans bounded.shape.writes⟩
  · intro index member
    exact (growth.values.values index).symbolicRootsRefine
      (bounded.values index (by simpa [growth.values.size] using member))
  · exact growth.canonicalMemory bounded.memory
  · intro value member mutability payload type reference
    exact Roots.Extends.atomsWithin (growth.values.values value)
      (bounded.holderValues value (by simpa [growth.values.size] using member) mutability payload type reference)
  · intro slot storage row member mutability payload type reference
    exact Roots.Extends.atomsWithin (growth.slots.values slot)
      (bounded.holderSlots slot storage row (by simpa [growth.slots.size] using member) mutability payload type reference)

#print axioms start_canonicalWithin
#print axioms State.Extends.canonicalWithin

end Goose.GIR.ReplacementContentFlow.Model

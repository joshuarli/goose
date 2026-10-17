import Goose.GIR.ReplacementContentFlowProofsSliceDependencyAtoms
import Goose.GIR.ReplacementContentFlowProofsCanonicalFacts

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def wholeOwnerReference : VTy → Bool
  | .data (.ref _ payload) => payload.ownerElem?.isSome
  | _ => false

def TouchFootprintAtom (func : Func) (policy : Atom → Prop) (atom : Atom) : Prop :=
  policy atom ∨ (∃ slot, atom = .local slot) ∨ (∃ index, atom = .contents index) ∨
    ∃ index type, atom = .param index ∧ func.params[index]? = some type ∧
      wholeOwnerReference (.data type) = false

structure State.TouchFootprint (func : Func) (types : Array (Option VTy))
    (policy : Atom → Prop) (state : State) : Prop where
  values : ∀ value, value < state.values.size → ∀ type,
    types[value]? = some (some type) → wholeOwnerReference type = false →
      (flowAt state.values value).AtomsWithin (TouchFootprintAtom func policy)
  slots : ∀ slot storage, func.slots[slot]? = some storage → slot < state.slots.size →
    wholeOwnerReference (.data storage.ty) = false →
      (flowAt state.slots slot).AtomsWithin (TouchFootprintAtom func policy)
  contents : ∀ index, index < state.contents.size →
    (flowAt state.contents index).AtomsWithin (TouchFootprintAtom func policy)
  writes : ∀ (index : Nat) (roots : Roots), state.writes[index]? = some (Write.assigned roots) →
    roots.AtomsWithin (TouchFootprintAtom func policy)
  returned : ∀ type, func.results = [type] → wholeOwnerReference (.data type) = false →
    state.returned.AtomsWithin (TouchFootprintAtom func policy)
  touched : state.touched.AtomsWithin (TouchFootprintAtom func policy)

theorem TouchFootprintAtom.local (func : Func) (policy : Atom → Prop) (slot : SlotId) :
    TouchFootprintAtom func policy (.local slot) := Or.inr (Or.inl ⟨slot,rfl⟩)

theorem TouchFootprintAtom.contents (func : Func) (policy : Atom → Prop) (index : Nat) :
    TouchFootprintAtom func policy (.contents index) := Or.inr (Or.inr (Or.inl ⟨index,rfl⟩))

theorem TouchFootprintAtom.parameter {func : Func} {policy : Atom → Prop} {index : Nat} {type : Ty}
    (row : func.params[index]? = some type) (interior : wholeOwnerReference (.data type) = false) :
    TouchFootprintAtom func policy (.param index) := Or.inr (Or.inr (Or.inr ⟨index,type,rfl,row,interior⟩))

theorem start_touchFootprint {module : Module} {func : Func} {types : Array (Option VTy)}
    {provenance : Prov} {results : Array (List RootRef)} (policy : Atom → Prop)
    (facts : FunctionCanonicalFacts module func types provenance results) :
    (start func types).TouchFootprint func types policy := by
  constructor
  · cases found : func.blocks[0]? with
    | none =>
        intro value bounded type _ _
        have bounded : value < func.numValues := by simpa [start,found] using bounded
        simp [start,found,flowAt,bounded,Roots.AtomsWithin]
    | some entry =>
        rw [start_values_fold types found]
        have base : ∀ value, value < (Array.replicate func.numValues Roots.pending).size → ∀ type,
            types[value]? = some (some type) → wholeOwnerReference type = false →
            (flowAt (Array.replicate func.numValues Roots.pending) value).AtomsWithin
              (TouchFootprintAtom func policy) := by
          intro value bounded type _ _
          have bounded : value < func.numValues := by simpa using bounded
          simp [flowAt,bounded,Roots.AtomsWithin]
        apply List.foldlRecOn (motive := fun values : Array Roots =>
          ∀ value, value < values.size → ∀ type, types[value]? = some (some type) →
            wholeOwnerReference type = false →
            (flowAt values value).AtomsWithin (TouchFootprintAtom func policy)) entry.params.zipIdx _ base
        intro values before pair member value bounded type typed interior
        have priorBound : value < values.size := by simpa using bounded
        change ((values.set! pair.1.1 _)[value]?.getD .unknown).AtomsWithin _
        simp only [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds]
        by_cases same : pair.1.1 = value
        · subst value
          obtain ⟨declared,_,canonical,formal⟩ := facts.parameters entry found pair.1 pair.2 member
          have identical : type = .data declared := Option.some.inj (Option.some.inj (typed.symm.trans canonical))
          subst type
          simp only [priorBound,ite_true,Option.getD_some]
          split
          · intro atom included
            have identical : atom = .param pair.2 := by simpa using included
            subst atom
            exact TouchFootprintAtom.parameter formal interior
          · simp [Roots.AtomsWithin]
        · simp only [same,ite_false]
          exact before value priorBound type typed interior
  · rw [start_components]
    intro slot storage row bounded _
    have bounded : slot < func.slots.size := by simpa using bounded
    simp [flowAt,bounded,Roots.AtomsWithin]
  · rw [start_components]
    intro index bounded
    have bounded : index < func.params.length := by simpa using bounded
    simp only [flowAt,Array.getElem?_mapIdx,Array.getElem?_eq_getElem (show index < func.params.toArray.size by simpa using bounded),
      Option.map_some,Option.getD_some]
    split
    · intro atom member
      have identical : atom = .contents index := by simpa using member
      subst atom
      exact TouchFootprintAtom.contents func policy index
    · simp [Roots.AtomsWithin]
  · rw [start_components]
    intro index roots row
    simp only [Array.getElem?_replicate] at row
    split at row <;> cases row
  · intro type _ _
    rw [start_returned]
    simp [Roots.AtomsWithin]
  · rw [start_components]
    simp [Roots.AtomsWithin]

#print axioms start_touchFootprint

end Goose.GIR.ReplacementContentFlow.Model

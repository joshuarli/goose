import Goose.GIR.ReplacementContentFlowProofsSliceCalls

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def SliceValues (func : Func) (types : Array (Option VTy)) (observed : List Atom) (values : Array Roots) : Prop :=
  ∀ value, value < values.size → ∀ mutability element,
    types[value]? = some (some (.data (.slice mutability element))) →
      (flowAt values value).AtomsWithin (SliceOrigin func observed)

structure State.SliceOrigins (func : Func) (types : Array (Option VTy)) (observed : List Atom)
    (state : State) : Prop where
  values : SliceValues func types observed state.values
  returned : ∀ mutability element, func.results = [.slice mutability element] →
    state.returned.AtomsWithin (SliceOrigin func observed)

theorem SliceValues.set {func : Func} {types : Array (Option VTy)} {observed : List Atom}
    {values : Array Roots} {index : Nat} {roots : Roots}
    (before : SliceValues func types observed values)
    (added : ∀ mutability element, types[index]? = some (some (.data (.slice mutability element))) →
      roots.AtomsWithin (SliceOrigin func observed)) :
    SliceValues func types observed (values.set! index roots) := by
  intro value bounded mutability element type
  have priorBound : value < values.size := by simpa using bounded
  change ((values.set! index roots)[value]?.getD .unknown).AtomsWithin _
  simp only [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds]
  by_cases same : index = value
  · subst value
    simpa [priorBound] using added mutability element type
  · simpa [same,flowAt] using before value priorBound mutability element type

theorem SliceValues.addFlow {func : Func} {types : Array (Option VTy)} {observed : List Atom}
    {values : Array Roots} {index : Nat} {roots : Roots}
    (before : SliceValues func types observed values)
    (added : ∀ mutability element, types[index]? = some (some (.data (.slice mutability element))) →
      roots.AtomsWithin (SliceOrigin func observed)) :
    SliceValues func types observed (addFlow values index roots) := by
  intro value bounded mutability element type
  have priorBound : value < values.size := by simpa [ReplacementContentFlow.Model.addFlow] using bounded
  rw [flowAt_addFlow]
  split
  · rename_i updated
    have same := updated.1
    subst value
    exact (before index priorBound mutability element type).join (added mutability element type)
  · exact before value priorBound mutability element type

theorem start_sliceOrigins {module : Module} {func : Func} {types : Array (Option VTy)}
    {provenance : Prov} {results : Array (List RootRef)} (observed : List Atom)
    (facts : FunctionCanonicalFacts module func types provenance results) :
    (start func types).SliceOrigins func types observed := by
  constructor
  · cases found : func.blocks[0]? with
    | none =>
        intro value bounded mutability element type
        have bounded : value < func.numValues := by simpa [start,found] using bounded
        simp [start,found,flowAt,bounded,Roots.AtomsWithin]
    | some entry =>
        rw [start_values_fold types found]
        have base : SliceValues func types observed (Array.replicate func.numValues .pending) := by
          intro value bounded mutability element type
          have bounded : value < func.numValues := by simpa using bounded
          simp [flowAt,bounded,Roots.AtomsWithin]
        apply List.foldlRecOn (motive := fun values : Array Roots => SliceValues func types observed values)
          entry.params.zipIdx _ base
        intro values before pair member
        apply before.set
        intro mutability element type
        obtain ⟨declared,_,canonical,formal⟩ := facts.parameters entry found pair.1 pair.2 member
        have identical : declared = .slice mutability element := by
          rw [canonical] at type
          exact VTy.data.inj (Option.some.inj (Option.some.inj type))
        subst declared
        have reference : valRefLike types pair.1.1 = true := by
          simp [valRefLike,canonical,VTy.refLike,Ty.isRefLike]
        simp only [reference,ite_true]
        intro atom member
        have same : atom = .param pair.2 := by simpa using member
        subst atom
        exact Or.inr ⟨pair.2,mutability,element,rfl,formal⟩
  · intro mutability element result
    rw [start_returned]
    simp [Roots.AtomsWithin]

theorem fixed_slice_load_atomsWithin {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {value address : ValueId}
    {mutability : Mutability} {element : Ty} {predicate : Atom → Prop}
    (fixed : step module states func types state (.def value (.load address)) = state)
    (typed : types[value]? = some (some (.data (.slice mutability element))))
    (bounded : state.touched.AtomsWithin predicate) :
    (flowAt state.values value).AtomsWithin predicate := by
  let before := touchValues types state (accessOperands (.def value (.load address)))
  let after := { before with values := addFlow before.values value (result func types before value (.load address)) }
  have fixedAfter : touchValues types after [value] = state := by
    simpa [after,before,step,interiorLoadedResults,loadedResults,typed,Ty.isRefLike,Ty.interiorTarget?] using fixed
  have reference : valRefLike types value = true := by simp [valRefLike,typed,VTy.refLike,Ty.isRefLike]
  have exposed : (touchValues types after [value]).touched.AtomsWithin predicate := by
    rw [fixedAfter]
    exact bounded
  have source := touchValues_source_atomsWithin (by simp : value ∈ [value]) reference exposed
  have values : after.values = state.values := by
    simpa only [touchValues_values] using congrArg State.values fixedAfter
  simpa only [values] using source

#print axioms start_sliceOrigins
#print axioms fixed_slice_load_atomsWithin

end Goose.GIR.ReplacementContentFlow.Model

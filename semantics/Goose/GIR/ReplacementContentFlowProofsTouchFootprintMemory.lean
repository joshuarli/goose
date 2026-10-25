import Goose.GIR.ReplacementContentFlowProofsTouchFootprint

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem State.TouchFootprint.addValue {func : Func} {types : Array (Option VTy)}
    {policy : Atom → Prop} {state : State} {value : ValueId} {roots : Roots}
    (before : state.TouchFootprint func types policy)
    (added : ∀ type, types[value]? = some (some type) → wholeOwnerReference type = false →
      roots.AtomsWithin (TouchFootprintAtom func policy)) :
    ({ state with values := addFlow state.values value roots } : State).TouchFootprint func types policy := by
  refine ⟨?_,before.slots,before.contents,before.writes,before.returned,before.touched⟩
  intro source bounded type typed interior
  have priorBound : source < state.values.size := by simpa [addFlow] using bounded
  rw [flowAt_addFlow]
  split
  · rename_i changed
    have same := changed.1
    subst source
    exact (before.values value priorBound type typed interior).join (added type typed interior)
  · exact before.values source priorBound type typed interior

theorem State.TouchFootprint.touch {func : Func} {types : Array (Option VTy)}
    {policy : Atom → Prop} {state : State} {touched : Roots}
    (before : state.TouchFootprint func types policy)
    (bounded : touched.AtomsWithin (TouchFootprintAtom func policy)) :
    ({ state with touched } : State).TouchFootprint func types policy :=
  ⟨before.values,before.slots,before.contents,before.writes,before.returned,bounded⟩

theorem State.TouchFootprint.touchValues {func : Func} {types : Array (Option VTy)}
    {policy : Atom → Prop} {state : State} {values : List ValueId}
    (before : state.TouchFootprint func types policy)
    (sources : ∀ value ∈ values, valRefLike types value = true →
      (flowAt state.values value).AtomsWithin (TouchFootprintAtom func policy)) :
    (Model.touchValues types state values).TouchFootprint func types policy := by
  apply before.touch
  apply List.foldlRecOn (motive := fun roots : Roots => roots.AtomsWithin (TouchFootprintAtom func policy))
    values _ before.touched
  intro current valid value member
  split
  · exact valid.join (sources value member ‹_›)
  · exact valid

theorem State.TouchFootprint.content {func : Func} {types : Array (Option VTy)}
    {policy : Atom → Prop} {state : State} {payload : Ty}
    {upper : List RootRef} {address : Roots}
    (before : state.TouchFootprint func types policy)
    (shape : state.Shape func)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (physical : HolderRoots func payload upper address)
    (reference : payload.isRefLike = true)
    (interior : wholeOwnerReference (.data payload) = false) :
    (Model.content func state address).AtomsWithin (TouchFootprintAtom func policy) := by
  cases address with
  | pending => trivial
  | unknown => exact False.elim physical
  | known atoms =>
      apply Roots.AtomsWithin.bind_known
      intro atom member
      cases physical atom member with
      | slot slot storage row type _ =>
          apply before.slots slot storage row
          · rw [shape.slots]
            exact (Array.getElem?_eq_some_iff.mp row).1
          · simpa only [type] using interior
      | parameter index mutability row _ =>
          have slice := paramOk_refLike_payload parameters row reference
          have found : (func.params[index]?).any Ty.isRefSlice = true := by simp [row,slice]
          simp only [found,ite_true]
          apply before.contents index
          rw [shape.contents]
          exact (List.getElem?_eq_some_iff.mp row).1

theorem State.TouchFootprint.addSlot {func : Func} {types : Array (Option VTy)}
    {policy : Atom → Prop} {state : State} {slot : SlotId} {roots : Roots}
    (before : state.TouchFootprint func types policy)
    (added : ∀ storage, func.slots[slot]? = some storage →
      wholeOwnerReference (.data storage.ty) = false →
      roots.AtomsWithin (TouchFootprintAtom func policy)) :
    ({ state with slots := addFlow state.slots slot roots } : State).TouchFootprint func types policy := by
  refine ⟨before.values,?_,before.contents,before.writes,before.returned,before.touched⟩
  intro source storage row bounded interior
  have priorBound : source < state.slots.size := by simpa [addFlow] using bounded
  rw [flowAt_addFlow]
  split
  · rename_i changed
    have same := changed.1
    subst source
    exact (before.slots slot storage row priorBound interior).join (added storage row interior)
  · exact before.slots source storage row priorBound interior

theorem State.TouchFootprint.addContent {func : Func} {types : Array (Option VTy)}
    {policy : Atom → Prop} {state : State} {index : Nat} {roots : Roots}
    (before : state.TouchFootprint func types policy)
    (added : roots.AtomsWithin (TouchFootprintAtom func policy)) :
    ({ state with
       contents := addFlow state.contents index roots
       writes := state.writes.set! index
        ((state.writes[index]?.getD (.assigned .unknown)).join (.assigned roots)) } : State).TouchFootprint func types policy := by
  refine ⟨before.values,before.slots,?_,?_,before.returned,before.touched⟩
  · intro source bounded
    have priorBound : source < state.contents.size := by simpa [addFlow] using bounded
    rw [flowAt_addFlow]
    split
    · rename_i changed
      have same := changed.1
      subst source
      exact (before.contents index priorBound).join added
    · exact before.contents source priorBound
  · intro source actual row
    simp only [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds] at row
    by_cases same : index = source
    · subst source
      by_cases bounded : index < state.writes.size
      · simp only [ite_true, bounded] at row
        cases prior : state.writes[index]? with
        | none =>
            have impossible := Array.getElem?_eq_none_iff.mp prior
            omega
        | some write =>
            rw [prior] at row
            cases write with
            | unchanged =>
                simp only [Option.getD_some,Write.join,Option.some.injEq,Write.assigned.injEq] at row
                subst actual
                exact added
            | assigned old =>
                simp only [Option.getD_some,Write.join,Option.some.injEq,Write.assigned.injEq] at row
                subst actual
                exact (before.writes index old prior).join added
      · simp [bounded] at row
    · simp only [same,ite_false] at row
      exact before.writes source actual row

theorem State.TouchFootprint.write {func : Func} {types : Array (Option VTy)}
    {policy : Atom → Prop} {state : State} {payload : Ty} {upper : List RootRef} {address roots : Roots}
    (before : state.TouchFootprint func types policy)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (physical : HolderRoots func payload upper address)
    (reference : payload.isRefLike = true)
    (added : wholeOwnerReference (.data payload) = false →
      roots.AtomsWithin (TouchFootprintAtom func policy)) :
    (Model.write func state address roots).TouchFootprint func types policy := by
  cases address with
  | pending => exact before
  | unknown => exact False.elim physical
  | known atoms =>
      simp only [Model.write]
      apply List.foldlRecOn (motive := fun current : State => current.TouchFootprint func types policy)
        atoms _ before
      intro current valid atom member
      cases physical atom member with
      | slot slot storage row type _ =>
          apply valid.addSlot
          intro actual actualAt interior
          have same : actual = storage := Option.some.inj (actualAt.symm.trans row)
          subst actual
          exact added (by simpa only [type] using interior)
      | parameter index mutability row _ =>
          have slice := paramOk_refLike_payload parameters row reference
          have found : (func.params[index]?).any Ty.isRefSlice = true := by simp [row,slice]
          simp only [found,ite_true]
          apply valid.addContent
          apply added
          cases payload <;> simp_all [Ty.isRefSlice,wholeOwnerReference]

theorem State.TouchFootprint.edge {func : Func} {types : Array (Option VTy)} {policy : Atom → Prop}
    {state : State} {target : BlockId} {args : List ValueId} {block : Block}
    (before : state.TouchFootprint func types policy) (size : state.values.size = func.numValues)
    (targetAt : func.blocks[target]? = some block)
    (passing : ∀ parameter argument, (parameter,argument) ∈ block.params.zip args →
      types[parameter.1]? = types[argument]? ∧ argument < func.numValues) :
    (Model.edge func state target args).TouchFootprint func types policy := by
  simp only [Model.edge,targetAt]
  have result : ((block.params.zip args).foldl (fun state pair =>
      { state with values := addFlow state.values pair.1.1 (flowAt state.values pair.2) }) state).TouchFootprint func types policy ∧
      ((block.params.zip args).foldl (fun state pair =>
        { state with values := addFlow state.values pair.1.1 (flowAt state.values pair.2) }) state).values.size = func.numValues := by
    apply List.foldlRecOn (motive := fun current : State => current.TouchFootprint func types policy ∧
      current.values.size = func.numValues) (block.params.zip args) _ ⟨before,size⟩
    intro current valid pair member
    obtain ⟨same,bounded⟩ := passing pair.1 pair.2 member
    constructor
    · apply valid.1.addValue
      intro type typed interior
      rw [same] at typed
      exact valid.1.values pair.2 (by rw [valid.2]; exact bounded) type typed interior
    · simpa [addFlow] using valid.2
  exact result.1

theorem State.TouchFootprint.ret {func : Func} {types : Array (Option VTy)} {policy : Atom → Prop}
    {state : State} {value : ValueId} {type : Ty}
    (before : state.TouchFootprint func types policy) (bounded : value < state.values.size)
    (result : func.results = [type]) (typed : types[value]? = some (some (.data type))) :
    ({ state with returned := state.returned.join (flowAt state.values value) } : State).TouchFootprint func types policy := by
  refine ⟨before.values,before.slots,before.contents,before.writes,?_,before.touched⟩
  intro actual actualAt interior
  have same : actual = type := (by simpa using actualAt.symm.trans result)
  subst actual
  exact (before.returned type result interior).join (before.values value bounded (.data type) typed interior)

#print axioms State.TouchFootprint.content
#print axioms State.TouchFootprint.addContent

end Goose.GIR.ReplacementContentFlow.Model

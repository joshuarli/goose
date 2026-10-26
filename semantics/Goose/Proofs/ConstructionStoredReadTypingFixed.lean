import Goose.Proofs.ConstructionAcceptedState
import Goose.Proofs.ConstructionReadTypingLayout
import Goose.Proofs.ExitExecutionStoredChildBacking
import Init.Data.List.Monadic

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation

private theorem mapM_success {α β ε : Type} (items : List α) (action : α → Except ε β)
    (values : List β) (executed : items.mapM action = .ok values) :
    values.length = items.length ∧
      (∀ value ∈ values, ∃ item, item ∈ items ∧ action item = .ok value) ∧
      (∀ (index : Nat) item value, items[index]? = some item → values[index]? = some value → action item = .ok value) := by
  induction items generalizing values with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at executed
    subst values
    exact ⟨rfl, by simp, by simp⟩
  | cons first rest ih =>
    simp only [List.mapM_cons, bind, Except.bind] at executed
    cases firstResult : action first with
    | error reason => simp only [firstResult] at executed; cases executed
    | ok head =>
      simp only [firstResult] at executed
      cases restResult : rest.mapM action with
      | error reason => simp only [restResult] at executed; cases executed
      | ok tail =>
        simp only [restResult, pure, Except.pure, Except.ok.injEq] at executed
        subst values
        obtain ⟨length, members, indexed⟩ := ih tail restResult
        refine ⟨by simpa only [List.length_cons] using congrArg Nat.succ length, ?_, ?_⟩
        · intro value member
          rcases List.mem_cons.mp member with same | member
          · subst value
            exact ⟨first, List.mem_cons_self, firstResult⟩
          · obtain ⟨item, present, result⟩ := members value member
            exact ⟨item, List.mem_cons_of_mem _ present, result⟩
        · intro index item value present found
          cases index with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at present found
            subst item
            subst value
            exact firstResult
          | succ index =>
            exact indexed index item value present found

private theorem fixedByteSize_variableElement (layout : LayoutEnv) (ty : Ty) (width : Nat)
    (sized : fixedByteSize? layout ty = some width) : ty.variableElement = false := by
  cases ty <;> try rfl
  case arr element count =>
    cases child : fixedByteSize? layout element with
    | none => simp only [fixedByteSize?, child, Option.map_none] at sized; cases sized
    | some width => exact fixedByteSize_variableElement layout element width child
  case varr element => cases sized
termination_by sizeOf ty

private theorem fixedValue_typed_of_layout (layout : LayoutEnv) (types : RootTypes) (state : ExecutionState)
    (conforms : Ty → Prop)
    (arrayElement : ∀ element count, conforms (.arr element count) → conforms element)
    (structFields : ∀ id fields descriptor, conforms (.structT id fields) → layout.structs[id]? = some descriptor →
      fields.toList = descriptor.fields.toList.map (·.ty) ∧ ∀ field ∈ descriptor.fields.toList, conforms field.ty)
    (fuel : Nat) (ty : Ty) (bytes : ByteArray) (start : Nat) (value : Value)
    (valid : conforms ty) (executed : fixedValue fuel layout ty bytes start = .ok value) :
    ValueRepresentation ty value ∧ PointerTypedValue types ty value ∧ ValueStorageBacked layout state value := by
  induction fuel generalizing ty start value with
  | zero => cases executed
  | succ fuel ih =>
    cases ty with
    | int ty =>
      cases integer : bytesInt ty bytes start <;>
        simp only [fixedValue, integer, bind, Except.bind, Except.mapError, pure, Except.pure] at executed
      · cases executed
      · cases executed; exact ⟨.integer _ _, .integer _ _, .integer _ _⟩
    | bool =>
      cases found : bytes.data[start]? <;> simp only [fixedValue, found, pure, Except.pure] at executed
      · cases executed
      · cases executed; exact ⟨.boolean _, .boolean _, .boolean _⟩
    | arr element count =>
      cases sized : fixedByteSize? layout element with
      | none => simp only [fixedValue, sized] at executed; cases executed
      | some width =>
        cases decoded : (List.range count).mapM
            (fun index => fixedValue fuel layout element bytes (start + index * width)) with
        | error reason => simp only [fixedValue, sized, decoded, bind, Except.bind] at executed; cases executed
        | ok values =>
          simp only [fixedValue, sized, decoded, bind, Except.bind, pure, Except.pure] at executed
          cases executed
          obtain ⟨length, members, indexed⟩ := mapM_success _ _ _ decoded
          have children : ∀ child ∈ values.toArray.toList,
              ValueRepresentation element child ∧ PointerTypedValue types element child ∧ ValueStorageBacked layout state child := by
            intro child member
            obtain ⟨index, inside, decoded⟩ := members child (by simpa only [List.toList_toArray] using member)
            exact ih element _ child (arrayElement element count valid) decoded
          refine ⟨.array element count values.toArray ?_ ?_ (fun child member => (children child member).1),
            .array element count values.toArray (fun child member => (children child member).2.1),
            .array values.toArray (fun child member => (children child member).2.2)⟩
          · exact fixedByteSize_variableElement layout element width sized
          · simpa only [List.size_toArray, List.length_range] using length
    | structT id fields =>
      cases descriptor : layout.structs[id]? with
      | none => simp only [fixedValue, descriptor] at executed; cases executed
      | some definition =>
        obtain ⟨fieldTypes, fieldConforms⟩ := structFields id fields definition valid descriptor
        cases decoded : definition.fields.toList.mapM
            (fun field => fixedValue fuel layout field.ty bytes (start + field.byteOffset)) with
        | error reason => simp only [fixedValue, descriptor, decoded, bind, Except.bind] at executed; cases executed
        | ok values =>
          simp only [fixedValue, descriptor, decoded, bind, Except.bind, pure, Except.pure] at executed
          cases executed
          obtain ⟨length, members, indexed⟩ := mapM_success _ _ _ decoded
          have children : ∀ (index : Nat) (ty : Ty) (child : Value), fields.toList[index]? = some ty →
              values.toArray[index]? = some child →
              ValueRepresentation ty child ∧ PointerTypedValue types ty child ∧ ValueStorageBacked layout state child := by
            intro index ty child declared present
            rw [fieldTypes, List.getElem?_map] at declared
            obtain ⟨field, selected, type⟩ := Option.map_eq_some_iff.mp declared
            subst ty
            apply ih field.ty _ child (fieldConforms field (List.mem_of_getElem? selected))
            exact indexed index field child selected (by simpa only [List.getElem?_toArray] using present)
          refine ⟨.record id fields values.toArray ?_ (fun index ty child declared present => (children index ty child declared present).1),
            .record id fields values.toArray (fun index ty child declared present => (children index ty child declared present).2.1),
            .record id values.toArray ?_⟩
          · simpa only [List.size_toArray, fieldTypes, List.length_map] using length
          · intro child member
            obtain ⟨field, present, decoded⟩ := members child (by simpa only [List.toList_toArray] using member)
            exact (ih field.ty _ child (fieldConforms field present) decoded).2.2
    | _ => cases executed

theorem fixedValue_typed (fuel : Nat) (layout : LayoutEnv) (types : RootTypes) (state : ExecutionState)
    (ty : Ty) (bytes : ByteArray) (start : Nat) (value : Value)
    (conforms : LayoutConforms layout ty) (executed : fixedValue fuel layout ty bytes start = .ok value) :
    ValueRepresentation ty value ∧ PointerTypedValue types ty value ∧ ValueStorageBacked layout state value := by
  apply fixedValue_typed_of_layout layout types state (LayoutConforms layout)
    (fun _ _ valid => valid) _ fuel ty bytes start value conforms executed
  intro id fields descriptor valid found
  obtain ⟨actual, present, declared, children⟩ := valid.descriptor layout id fields
  have same : actual = descriptor := Option.some.inj (present.symm.trans found)
  subst actual
  exact ⟨declared, children⟩

#print axioms fixedValue_typed

end Goose.Proofs.ConstructionAcceptedExecution

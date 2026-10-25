import Goose.Proofs.Memory
import Goose.Core.Sound.Store

namespace Goose.Evidence

open Goose.Core Goose.Proofs.Memory

abbrev RootDeclarations := RootInst → Option Ty

def RootDeclarations.Extends (before after : RootDeclarations) : Prop :=
  ∀ root ty, before root = some ty → after root = some ty

inductive StoragePath : Ty → List Nat → Ty → Prop
  | root (ty : Ty) : StoragePath ty [] ty
  | fixed {element count index path result}
      (tail : StoragePath element path result) :
      StoragePath (.arr element count) (index :: path) result
  | grow {element index path result}
      (tail : StoragePath element path result) :
      StoragePath (.grow element) (index :: path) result
  | shrink {element index path result}
      (tail : StoragePath element path result) :
      StoragePath (.growshrink element) (index :: path) result
  | limited {element capacity index path result}
      (tail : StoragePath element path result) :
      StoragePath (.limited element capacity) (index :: path) result
  | field {sid fields index fieldTy path result}
      (field : fields.toList[index]? = some fieldTy)
      (tail : StoragePath fieldTy path result) :
      StoragePath (.structT sid fields) (index :: path) result

def DeclaredLocation (roots : RootDeclarations) (location : Loc) (ty : Ty) : Prop :=
  ∃ rootTy, roots location.root = some rootTy ∧ StoragePath rootTy location.path ty

theorem StoragePath.append {a b c : Ty} {p q : List Nat}
    (path : StoragePath a p b) (tail : StoragePath b q c) :
    StoragePath a (p ++ q) c := by
  induction path with
  | root => exact tail
  | fixed _ ih => exact .fixed (ih tail)
  | grow _ ih => exact .grow (ih tail)
  | shrink _ ih => exact .shrink (ih tail)
  | limited _ ih => exact .limited (ih tail)
  | field field _ ih => exact .field field (ih tail)

theorem DeclaredLocation.mono {before after : RootDeclarations} {location : Loc} {ty : Ty}
    (extension : before.Extends after) (declared : DeclaredLocation before location ty) :
    DeclaredLocation after location ty := by
  obtain ⟨rootTy, declaration, path⟩ := declared
  exact ⟨rootTy, extension _ _ declaration, path⟩

theorem DeclaredLocation.append {roots : RootDeclarations} {location : Loc} {a b : Ty}
    {path : List Nat} (declared : DeclaredLocation roots location a)
    (selection : StoragePath a path b) :
    DeclaredLocation roots ⟨location.root, location.path ++ path⟩ b := by
  obtain ⟨rootTy, declaration, initialPath⟩ := declared
  exact ⟨rootTy, declaration, initialPath.append selection⟩

theorem DeclaredLocation.ownerElement {roots : RootDeclarations} {location : Loc}
    {owner element : Ty} (declared : DeclaredLocation roots location owner)
    (ownerType : owner.ownerElem? = some element) (index : Nat) :
    DeclaredLocation roots ⟨location.root, location.path ++ [index]⟩ element := by
  cases owner with
  | grow other =>
    simp only [Ty.ownerElem?, Option.some.injEq] at ownerType
    subst other
    exact declared.append (.grow (.root element))
  | growshrink other =>
    simp only [Ty.ownerElem?, Option.some.injEq] at ownerType
    subst other
    exact declared.append (.shrink (.root element))
  | limited other capacity =>
    simp only [Ty.ownerElem?, Option.some.injEq] at ownerType
    subst other
    exact declared.append (.limited (.root element))
  | _ => simp [Ty.ownerElem?] at ownerType

theorem StoragePath.get {rootTy result : Ty} {path : List Nat} {value selected : Val}
    (declared : StoragePath rootTy path result) (typed : FlatTy rootTy value)
    (read : value.get? path = some selected) : FlatTy result selected := by
  induction declared generalizing value with
  | root =>
    simp only [Val.get?, Option.some.injEq] at read
    subst selected
    exact typed
  | @fixed element count index path result tail ih =>
    cases value <;> simp only [FlatTy] at typed
    rename_i elements
    rw [get_fixed] at read
    cases present : elements[index]? with
    | none => simp [present] at read
    | some element =>
      simp only [present, Option.bind_some] at read
      exact ih (typed.2 _ element present) read
  | @grow element index path result tail ih | @shrink element index path result tail ih =>
    cases value <;> simp only [FlatTy] at typed
    rename_i elementTy elements
    rw [get_resizable] at read
    cases present : elements[index]? with
    | none => simp [present] at read
    | some element =>
      simp only [present, Option.bind_some] at read
      exact ih (typed.2 _ element present) read
  | @limited element capacity index path result tail ih =>
    cases value <;> simp only [FlatTy] at typed
    rename_i elementTy capacity elements len
    rw [get_limited] at read
    cases present : elements[index]? with
    | none => simp [present] at read
    | some element =>
      simp only [present, Option.bind_some] at read
      exact ih (typed.2.2.2.2 _ element present) read
  | @field sid types index fieldTy path result selector tail ih =>
    cases value <;> simp only [FlatTy] at typed
    rename_i sid fields
    obtain ⟨fieldValue, present, fieldTyped⟩ := fields_get _ _ typed.2 _ _ selector
    have arrayPresent : fields[index]? = some fieldValue := by simpa using present
    rw [get_record, arrayPresent] at read
    exact ih fieldTyped read

mutual
def WeakValueTy (roots : RootDeclarations) (value : Val) (ty : Ty) : Prop :=
  match ty, value with
  | .ref _ target, value => ∃ location, value = .ref location ∧ DeclaredLocation roots location target
  | .slice _ element, value => (∃ location start len arrayTy,
      value = .slice location start len ∧ DeclaredLocation roots location arrayTy ∧
      arrayTy.ownerElem? = some element) ∨
      ∃ location start len count,
        value = .slice location start len ∧ DeclaredLocation roots location (.arr element count)
  | .unit, value => value = .unit
  | .int ty, value => FlatTy (.int ty) value
  | .bool, value => FlatTy .bool value
  | .arr element count, .fixed elements => elements.size = count ∧
      ∀ (i : Nat) (value : Val), elements[i]? = some value → WeakValueTy roots value element
  | .grow element, .resizable stored elements
  | .growshrink element, .resizable stored elements => element = stored ∧
      ∀ (i : Nat) (value : Val), elements[i]? = some value → WeakValueTy roots value element
  | .limited element capacity, .limited stored storedCapacity slots len =>
      element = stored ∧ capacity = storedCapacity ∧ len ≤ capacity ∧ len ≤ slots.size ∧
      ∀ (i : Nat) (value : Val), slots[i]? = some value → WeakValueTy roots value element
  | .structT sid fields, .record stored values => sid = stored ∧ WeakFieldsTy roots fields values.toList
  | _, _ => False

def WeakFieldsTy (roots : RootDeclarations) : TyList → List Val → Prop
  | .nil, [] => True
  | .cons ty rest, value :: values => WeakValueTy roots value ty ∧ WeakFieldsTy roots rest values
  | _, _ => False
end

mutual
theorem WeakValueTy.ofFlat {roots : RootDeclarations} {ty : Ty} {value : Val}
    (typed : FlatTy ty value) : WeakValueTy roots value ty := by
  cases ty <;> cases value <;> simp only [FlatTy] at typed <;>
    try contradiction
  case int.int => exact typed
  case bool.bool => exact typed
  case arr.fixed =>
    exact ⟨typed.1, fun i value present => WeakValueTy.ofFlat (typed.2 i value present)⟩
  case grow.resizable =>
    exact ⟨typed.1, fun i value present => WeakValueTy.ofFlat (typed.2 i value present)⟩
  case growshrink.resizable =>
    exact ⟨typed.1, fun i value present => WeakValueTy.ofFlat (typed.2 i value present)⟩
  case limited.limited =>
    exact ⟨typed.1, typed.2.1, typed.2.2.1, typed.2.2.2.1,
      fun i value present => WeakValueTy.ofFlat (typed.2.2.2.2 i value present)⟩
  case structT.record => exact ⟨typed.1, WeakFieldsTy.ofFlat typed.2⟩
termination_by structural ty

theorem WeakFieldsTy.ofFlat {roots : RootDeclarations} {fields : TyList} {values : List Val}
    (typed : Goose.Proofs.Memory.FieldsTy fields values) : WeakFieldsTy roots fields values := by
  cases fields <;> cases values <;> simp only [Goose.Proofs.Memory.FieldsTy] at typed <;>
    try contradiction
  case nil.nil => trivial
  case cons.cons => exact ⟨WeakValueTy.ofFlat typed.1, WeakFieldsTy.ofFlat typed.2⟩
termination_by structural fields
end

mutual
theorem WeakValueTy.flat {roots : RootDeclarations} {ty : Ty} {value : Val}
    (flat : ty.flat = true) (typed : WeakValueTy roots value ty) : FlatTy ty value := by
  cases ty <;> cases value <;> simp only [Ty.flat] at flat <;>
    simp only [WeakValueTy] at typed <;> try contradiction
  case int.int => exact typed
  case bool.bool => exact typed
  case arr.fixed =>
    exact ⟨typed.1, fun i value present => WeakValueTy.flat flat (typed.2 i value present)⟩
  case structT.record => exact ⟨typed.1, WeakFieldsTy.flat flat typed.2⟩
termination_by structural ty

theorem WeakFieldsTy.flat {roots : RootDeclarations} {fields : TyList} {values : List Val}
    (flat : fields.flat = true) (typed : WeakFieldsTy roots fields values) :
    Goose.Proofs.Memory.FieldsTy fields values := by
  cases fields <;> cases values <;> simp only [WeakFieldsTy] at typed <;> try contradiction
  case nil.nil => trivial
  case cons.cons =>
    simp only [TyList.flat, Bool.and_eq_true] at flat
    exact ⟨WeakValueTy.flat flat.1 typed.1, WeakFieldsTy.flat flat.2 typed.2⟩
termination_by structural fields
end

mutual
theorem WeakValueTy.mono {before after : RootDeclarations} {ty : Ty} {value : Val}
    (extension : before.Extends after) (typed : WeakValueTy before value ty) : WeakValueTy after value ty := by
  cases ty with
  | ref permission target =>
    obtain ⟨location, same, declared⟩ := typed
    exact ⟨location, same, declared.mono extension⟩
  | slice permission element =>
    rcases typed with ⟨location, start, len, arrayTy, same, declared, elementType⟩ |
      ⟨location, start, len, count, same, declared⟩
    · exact Or.inl ⟨location, start, len, arrayTy, same, declared.mono extension, elementType⟩
    · exact Or.inr ⟨location, start, len, count, same, declared.mono extension⟩
  | unit | int _ | bool | tuple _ => exact typed
  | arr element count =>
    cases value <;> simp only [WeakValueTy] at typed ⊢ <;> try contradiction
    exact ⟨typed.1, fun i value present => WeakValueTy.mono extension (typed.2 i value present)⟩
  | grow element | growshrink element =>
    cases value <;> simp only [WeakValueTy] at typed ⊢ <;> try contradiction
    exact ⟨typed.1, fun i value present => WeakValueTy.mono extension (typed.2 i value present)⟩
  | limited element capacity =>
    cases value <;> simp only [WeakValueTy] at typed ⊢ <;> try contradiction
    exact ⟨typed.1, typed.2.1, typed.2.2.1, typed.2.2.2.1,
      fun i value present => WeakValueTy.mono extension (typed.2.2.2.2 i value present)⟩
  | structT sid fields =>
    cases value <;> simp only [WeakValueTy] at typed ⊢ <;> try contradiction
    exact ⟨typed.1, WeakFieldsTy.mono extension typed.2⟩
termination_by structural ty

theorem WeakFieldsTy.mono {before after : RootDeclarations} {fields : TyList} {values : List Val}
    (extension : before.Extends after) (typed : WeakFieldsTy before fields values) : WeakFieldsTy after fields values := by
  cases fields <;> cases values <;> simp only [WeakFieldsTy] at typed ⊢ <;> try contradiction
  case cons.cons => exact ⟨WeakValueTy.mono extension typed.1, WeakFieldsTy.mono extension typed.2⟩
termination_by structural fields
end

theorem WeakFieldsTy.get : ∀ (fields : TyList) (values : List Val), WeakFieldsTy roots fields values →
    ∀ (i : Nat) (ty : Ty), fields.toList[i]? = some ty →
      ∃ value, values[i]? = some value ∧ WeakValueTy roots value ty
  | .nil, values, typed, i, ty, selector => by simp [TyList.toList] at selector
  | .cons head rest, values, typed, i, ty, selector => by
    cases values with
    | nil => contradiction
    | cons value values =>
      cases i with
      | zero =>
        simp only [TyList.toList, List.getElem?_cons_zero, Option.some.injEq] at selector
        subst ty
        exact ⟨value, rfl, typed.1⟩
      | succ i =>
        exact WeakFieldsTy.get rest values typed.2 i ty (by simpa [TyList.toList] using selector)

theorem WeakFieldsTy.set {roots : RootDeclarations} {fields : TyList} {values : List Val}
    {index : Nat} {ty : Ty} {value : Val}
    (typed : WeakFieldsTy roots fields values) (selector : fields.toList[index]? = some ty)
    (replacement : WeakValueTy roots value ty) : WeakFieldsTy roots fields (values.set index value) := by
  cases fields with
  | nil => simp [TyList.toList] at selector
  | cons head rest =>
    cases values with
    | nil => contradiction
    | cons old values =>
      cases index with
      | zero =>
        simp only [TyList.toList, List.getElem?_cons_zero, Option.some.injEq] at selector
        subst ty
        exact ⟨replacement, typed.2⟩
      | succ index =>
        exact ⟨typed.1, WeakFieldsTy.set typed.2 (by simpa [TyList.toList] using selector) replacement⟩

termination_by structural fields


theorem WeakValueTy.get {roots : RootDeclarations} {rootTy result : Ty} {path : List Nat}
    {value selected : Val} (declared : StoragePath rootTy path result)
    (typed : WeakValueTy roots value rootTy) (read : value.get? path = some selected) :
    WeakValueTy roots selected result := by
  induction declared generalizing value with
  | root =>
    simp only [Val.get?, Option.some.injEq] at read
    subst selected
    exact typed
  | @fixed element count index path result tail ih =>
    cases value <;> simp only [WeakValueTy] at typed <;> try contradiction
    rename_i elements
    rw [get_fixed] at read
    cases present : elements[index]? with
    | none => simp [present] at read
    | some child =>
      simp only [present, Option.bind_some] at read
      exact ih (typed.2 index child present) read
  | @grow element index path result tail ih | @shrink element index path result tail ih =>
    cases value <;> simp only [WeakValueTy] at typed <;> try contradiction
    rename_i stored elements
    rw [get_resizable] at read
    cases present : elements[index]? with
    | none => simp [present] at read
    | some child =>
      simp only [present, Option.bind_some] at read
      exact ih (typed.2 index child present) read
  | @limited element capacity index path result tail ih =>
    cases value <;> simp only [WeakValueTy] at typed <;> try contradiction
    rename_i stored storedCapacity slots len
    rw [get_limited] at read
    cases present : slots[index]? with
    | none => simp [present] at read
    | some child =>
      simp only [present, Option.bind_some] at read
      exact ih (typed.2.2.2.2 index child present) read
  | @field sid fields index fieldTy path result selector tail ih =>
    cases value <;> simp only [WeakValueTy] at typed <;> try contradiction
    rename_i stored values
    obtain ⟨child, present, childTyped⟩ := WeakFieldsTy.get fields values.toList typed.2 index fieldTy selector
    have arrayPresent : values[index]? = some child := by simpa using present
    rw [get_record, arrayPresent] at read
    exact ih childTyped read

theorem elements_set {roots : RootDeclarations} {element : Ty} {values : Array Val}
    {index : Nat} (bound : index < values.size) {replacement : Val}
    (typed : ∀ (i : Nat) (value : Val), values[i]? = some value → WeakValueTy roots value element)
    (newTyped : WeakValueTy roots replacement element) :
    ∀ (i : Nat) (value : Val), (values.set index replacement bound)[i]? = some value → WeakValueTy roots value element := by
  intro i value present
  rw [Array.getElem?_set] at present
  split at present
  · cases present
    exact newTyped
  · exact typed i value present

theorem WeakValueTy.modifyAt {roots : RootDeclarations} {rootTy result : Ty} {path : List Nat}
    {value changed : Val} {f : Val → Option Val}
    (declared : StoragePath rootTy path result) (typed : WeakValueTy roots value rootTy)
    (modified : value.modifyAt? path f = some changed)
    (preserve : ∀ old new, WeakValueTy roots old result → f old = some new → WeakValueTy roots new result) :
    WeakValueTy roots changed rootTy := by
  induction declared generalizing value changed with
  | root => exact preserve value changed typed modified
  | @fixed element count index path result tail ih =>
    cases value <;> simp only [WeakValueTy] at typed <;> try contradiction
    rename_i values
    simp only [Val.modifyAt?] at modified
    split at modified
    · rename_i bound
      cases childChange : values[index].modifyAt? path f with
      | none => simp [childChange] at modified
      | some replacement =>
        simp only [childChange, Option.some.injEq] at modified
        subst changed
        have childTyped := ih (typed.2 index values[index] (by simp)) childChange preserve
        exact ⟨by simpa using typed.1, elements_set bound typed.2 childTyped⟩
    · contradiction
  | @grow element index path result tail ih | @shrink element index path result tail ih =>
    cases value <;> simp only [WeakValueTy] at typed <;> try contradiction
    rename_i stored values
    simp only [Val.modifyAt?] at modified
    split at modified
    · rename_i bound
      cases childChange : values[index].modifyAt? path f with
      | none => simp [childChange] at modified
      | some replacement =>
        simp only [childChange, Option.some.injEq] at modified
        subst changed
        have childTyped := ih (typed.2 index values[index] (by simp)) childChange preserve
        exact ⟨typed.1, elements_set bound typed.2 childTyped⟩
    · contradiction
  | @limited element capacity index path result tail ih =>
    cases value <;> simp only [WeakValueTy] at typed <;> try contradiction
    rename_i stored storedCapacity slots len
    simp only [Val.modifyAt?] at modified
    split at modified
    · rename_i bound
      cases childChange : slots[index].modifyAt? path f with
      | none => simp [childChange] at modified
      | some replacement =>
        simp only [childChange, Option.some.injEq] at modified
        subst changed
        have childTyped := ih (typed.2.2.2.2 index slots[index] (by simp)) childChange preserve
        exact ⟨typed.1, typed.2.1, typed.2.2.1, by simpa using typed.2.2.2.1,
          elements_set bound typed.2.2.2.2 childTyped⟩
    · contradiction
  | @field sid fields index fieldTy path result selector tail ih =>
    cases value <;> simp only [WeakValueTy] at typed <;> try contradiction
    rename_i stored values
    simp only [Val.modifyAt?] at modified
    split at modified
    · rename_i bound
      cases childChange : values[index].modifyAt? path f with
      | none => simp [childChange] at modified
      | some replacement =>
        simp only [childChange, Option.some.injEq] at modified
        subst changed
        obtain ⟨child, present, oldTyped⟩ := WeakFieldsTy.get fields values.toList typed.2 index fieldTy selector
        have arrayPresent : values[index]? = some child := by simpa using present
        rw [Array.getElem?_eq_getElem bound] at arrayPresent
        cases arrayPresent
        have childTyped := ih oldTyped childChange preserve
        refine ⟨typed.1, ?_⟩
        rw [Array.toList_set]
        exact WeakFieldsTy.set typed.2 selector childTyped
    · contradiction


theorem elements_extract {roots : RootDeclarations} {element : Ty} {values : Array Val}
    (typed : ∀ (i : Nat) (value : Val), values[i]? = some value → WeakValueTy roots value element)
    (start stop : Nat) :
    ∀ (i : Nat) (value : Val), (values.extract start stop)[i]? = some value → WeakValueTy roots value element := by
  intro i value present
  rw [Array.getElem?_extract] at present
  split at present
  · exact typed (start + i) value present
  · contradiction

theorem elements_append {roots : RootDeclarations} {element : Ty} {left right : Array Val}
    (leftTyped : ∀ (i : Nat) (value : Val), left[i]? = some value → WeakValueTy roots value element)
    (rightTyped : ∀ (i : Nat) (value : Val), right[i]? = some value → WeakValueTy roots value element) :
    ∀ (i : Nat) (value : Val), (left ++ right)[i]? = some value → WeakValueTy roots value element := by
  intro i value present
  by_cases leftBound : i < left.size
  · rw [Array.getElem?_append_left leftBound] at present
    exact leftTyped i value present
  · rw [Array.getElem?_append_right (by omega)] at present
    exact rightTyped (i - left.size) value present

theorem WeakValueTy.appendOwner {roots : RootDeclarations} {owner element : Ty} {old new : Val}
    {values : Array Val} (ownerType : owner.ownerElem? = some element)
    (typed : WeakValueTy roots old owner)
    (valuesTyped : ∀ (i : Nat) (value : Val), values[i]? = some value → WeakValueTy roots value element)
    (appended : old.appendAll values = some new) : WeakValueTy roots new owner := by
  cases owner <;> simp only [Ty.ownerElem?] at ownerType <;> try contradiction
  all_goals simp only [Option.some.injEq] at ownerType; subst element
  case grow element =>
    cases old <;> simp only [WeakValueTy] at typed <;> try contradiction
    simp only [Val.appendAll, Option.some.injEq] at appended
    subst new
    exact ⟨typed.1, elements_append typed.2 valuesTyped⟩
  case growshrink element =>
    cases old <;> simp only [WeakValueTy] at typed <;> try contradiction
    simp only [Val.appendAll, Option.some.injEq] at appended
    subst new
    exact ⟨typed.1, elements_append typed.2 valuesTyped⟩
  case limited element capacity =>
    cases old <;> simp only [WeakValueTy] at typed <;> try contradiction
    rename_i stored storedCapacity slots len
    obtain ⟨rfl, rfl, withinCapacity, withinSlots, slotsTyped⟩ := typed
    simp only [Val.appendAll] at appended
    split at appended
    · rename_i capacityBound
      have size := limitedAppendSlots_written_size slots values len withinSlots
      have extent := limitedAppendSlots_written_le_size slots values len
      simp only [Option.some.injEq] at appended
      subst new
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩
      · simpa only [Array.size_append, Array.size_extract, Nat.min_eq_left withinSlots,
          Nat.sub_zero] using capacityBound
      · exact extent
      · exact elements_append (elements_append (elements_extract slotsTyped 0 len) valuesTyped)
          (elements_extract slotsTyped _ _)
    · contradiction

theorem WeakValueTy.truncateOwner {roots : RootDeclarations} {owner element : Ty} {old new : Val}
    {len : Nat} (ownerType : owner.ownerElem? = some element)
    (typed : WeakValueTy roots old owner) (truncated : old.truncate len = some new) : WeakValueTy roots new owner := by
  cases owner <;> simp only [Ty.ownerElem?] at ownerType <;> try contradiction
  all_goals simp only [Option.some.injEq] at ownerType; subst element
  case grow element =>
    cases old <;> simp only [WeakValueTy] at typed <;> try contradiction
    simp only [Val.truncate] at truncated
    split at truncated
    · simp only [Option.some.injEq] at truncated
      subst new
      exact ⟨typed.1, elements_extract typed.2 0 len⟩
    · contradiction
  case growshrink element =>
    cases old <;> simp only [WeakValueTy] at typed <;> try contradiction
    simp only [Val.truncate] at truncated
    split at truncated
    · simp only [Option.some.injEq] at truncated
      subst new
      exact ⟨typed.1, elements_extract typed.2 0 len⟩
    · contradiction
  case limited element capacity =>
    cases old <;> simp only [WeakValueTy] at typed <;> try contradiction
    rename_i stored storedCapacity slots oldLen
    simp only [Val.truncate] at truncated
    split at truncated
    · rename_i shorter
      simp only [Option.some.injEq] at truncated
      subst new
      exact ⟨typed.1, typed.2.1, Nat.le_trans shorter typed.2.2.1,
        Nat.le_trans shorter typed.2.2.2.1, typed.2.2.2.2⟩
    · contradiction


def WeakStoreTy (roots : RootDeclarations) (store : Store) : Prop :=
  ∀ root value, store.roots[root]? = some value →
    ∃ ty, roots root = some ty ∧ WeakValueTy roots value ty

theorem WeakStoreTy.mono {before after : RootDeclarations} {store : Store}
    (extension : before.Extends after) (typed : WeakStoreTy before store) : WeakStoreTy after store := by
  intro root value present
  obtain ⟨ty, declaration, valueTyped⟩ := typed root value present
  exact ⟨ty, extension _ _ declaration, valueTyped.mono extension⟩

theorem WeakStoreTy.release {roots : RootDeclarations} {store : Store} {root : RootInst}
    (typed : WeakStoreTy roots store) : WeakStoreTy roots (store.release root) := by
  intro other value present
  simp only [Store.release, Std.HashMap.getElem?_erase] at present
  split at present
  · contradiction
  · exact typed other value present

theorem WeakStoreTy.empty (roots : RootDeclarations) : WeakStoreTy roots Store.empty := by
  intro root value present
  simp [Store.empty] at present

theorem WeakStoreTy.introduce {roots : RootDeclarations} {store : Store} {root : RootInst}
    {value : Val} {ty : Ty} (typed : WeakStoreTy roots store)
    (declared : roots root = some ty) (valueTyped : WeakValueTy roots value ty) :
    WeakStoreTy roots (store.introduce root value) := by
  intro other stored present
  simp only [Store.introduce, Std.HashMap.getElem?_insert] at present
  split at present
  · rename_i same
    have sameRoot : root = other := eq_of_beq same
    subst other
    cases present
    exact ⟨ty, declared, valueTyped⟩
  · exact typed other stored present

theorem WeakStoreTy.read {roots : RootDeclarations} {store : Store} {location : Loc}
    {ty : Ty} {value : Val} (typed : WeakStoreTy roots store)
    (declared : DeclaredLocation roots location ty) (read : store.read location = .ok value) :
    WeakValueTy roots value ty := by
  obtain ⟨rootTy, declaration, path⟩ := declared
  obtain ⟨rootValue, present, selected⟩ := (read_ok_iff _ _ _).mp read
  obtain ⟨storedTy, storedDeclaration, storedTyped⟩ := typed location.root rootValue present
  have same : storedTy = rootTy := Option.some.inj (storedDeclaration.symm.trans declaration)
  subst storedTy
  exact storedTyped.get path selected

theorem WeakStoreTy.modify {roots : RootDeclarations} {before after : Store} {location : Loc}
    {ty : Ty} {f : Val → Option Val} (typed : WeakStoreTy roots before)
    (target : DeclaredLocation roots location ty)
    (preserve : ∀ old new, WeakValueTy roots old ty → f old = some new → WeakValueTy roots new ty)
    (modified : before.modify location f = .ok after) : WeakStoreTy roots after := by
  obtain ⟨rootTy, declaration, path⟩ := target
  obtain ⟨old, selected, new, rebuilt, rootPresent, oldRead, replaced, changed, rootMap⟩ :=
    modify_spec before after location f modified
  obtain ⟨storedTy, storedDeclaration, oldTyped⟩ := typed location.root old rootPresent
  have sameTy : storedTy = rootTy := Option.some.inj (storedDeclaration.symm.trans declaration)
  subst storedTy
  have newTyped := oldTyped.modifyAt path changed preserve
  intro root value present
  rw [rootMap, Goose.Core.Sound.get_reinsert] at present
  by_cases same : location.root = root
  · subst root
    simp only [↓reduceIte, Option.some.injEq] at present
    subst value
    exact ⟨rootTy, declaration, newTyped⟩
  · simp only [same, ↓reduceIte] at present
    exact typed root value present

theorem WeakStoreTy.write {roots : RootDeclarations} {before after : Store} {location : Loc}
    {ty : Ty} {value : Val} (typed : WeakStoreTy roots before)
    (target : DeclaredLocation roots location ty) (valueTyped : WeakValueTy roots value ty)
    (written : before.write location value = .ok after) : WeakStoreTy roots after := by
  apply typed.modify target _ written
  intro old new oldTyped replaced
  cases replaced
  exact valueTyped

theorem WeakStoreTy.appendOwner {roots : RootDeclarations} {before after : Store}
    {location : Loc} {values : Array Val} {owner element : Ty} {index : Nat}
    (typed : WeakStoreTy roots before) (target : DeclaredLocation roots location owner)
    (ownerType : owner.ownerElem? = some element)
    (valuesTyped : ∀ (i : Nat) (value : Val), values[i]? = some value → WeakValueTy roots value element)
    (appended : before.append location values = .ok (after, index)) : WeakStoreTy roots after := by
  apply typed.modify target (fun _old _new oldTyped changed => oldTyped.appendOwner ownerType valuesTyped changed)
  rcases append_spec before after location values index appended with
    ⟨elementTy, elements, read, size, modified⟩ |
    ⟨elementTy, capacity, slots, len, read, size, modified⟩
  all_goals exact modified

theorem WeakStoreTy.truncateOwner {roots : RootDeclarations} {before after : Store}
    {location : Loc} {owner element : Ty} {len : Nat}
    (typed : WeakStoreTy roots before) (target : DeclaredLocation roots location owner)
    (ownerType : owner.ownerElem? = some element) (truncated : before.truncate location len = .ok after) :
    WeakStoreTy roots after :=
  typed.modify target (fun _old _new oldTyped changed => oldTyped.truncateOwner ownerType changed) truncated


theorem WeakValueTy.int {roots : RootDeclarations} {value : Val} {ty : IntTy}
    (typed : WeakValueTy roots value (.int ty)) : ∃ n, value = .int ty n := by
  cases value <;> simp_all [WeakValueTy, FlatTy]

theorem WeakValueTy.bool {roots : RootDeclarations} {value : Val}
    (typed : WeakValueTy roots value .bool) : ∃ b, value = .bool b := by
  cases value <;> simp_all [WeakValueTy, FlatTy]

theorem WeakValueTy.passable {roots : RootDeclarations} {value : Val} {source target : Ty}
    (typed : WeakValueTy roots value source) (passing : source.passableTo target = true) :
    WeakValueTy roots value target := by
  cases source <;> cases target <;>
    simp only [Ty.passableTo, Bool.and_eq_true, beq_iff_eq] at passing <;>
    first
    | (simp at passing; done)
    | (obtain ⟨rfl, _⟩ := passing; exact typed)
    | (cases passing; exact typed)
    | (injection passing with sameElement sameCount
       subst sameElement
       first | (subst sameCount; exact typed) | exact typed)
    | exact typed

theorem WeakStoreTy.readLoc {roots : RootDeclarations} {before after : St} {location : Loc}
    {ty : Ty} {value : Val} (typed : WeakStoreTy roots before.store)
    (declared : DeclaredLocation roots location ty)
    (read : Goose.Core.readLoc location before = .ok value after) :
    WeakValueTy roots value ty ∧ after = before := by
  unfold Goose.Core.readLoc at read
  cases stored : before.store.read location with
  | error fault => simp [stored] at read
  | ok found =>
    simp only [stored, Res.ok.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    exact ⟨typed.read declared stored, rfl⟩

theorem WeakStoreTy.writeFlat {roots : RootDeclarations} {before after : Store}
    {location : Loc} {value : Val} {ty : Ty} (typed : WeakStoreTy roots before)
    (target : DeclaredLocation roots location ty) (_flat : ty.flat = true)
    (valueTyped : WeakValueTy roots value ty) (written : before.write location value = .ok after) :
    WeakStoreTy roots after := typed.write target valueTyped written

theorem WeakStoreTy.writeReference {roots : RootDeclarations} {before after : Store}
    {location : Loc} {value : Val} {ty : Ty} (typed : WeakStoreTy roots before)
    (target : DeclaredLocation roots location ty) (_reference : ty.isRefLike = true)
    (valueTyped : WeakValueTy roots value ty) (written : before.write location value = .ok after) :
    WeakStoreTy roots after := typed.write target valueTyped written

theorem WeakStoreTy.writeReadable {roots : RootDeclarations} {before after : Store}
    {location : Loc} {value : Val} {ty : Ty} (typed : WeakStoreTy roots before)
    (target : DeclaredLocation roots location ty) (_readable : ty.readable = true)
    (valueTyped : WeakValueTy roots value ty) (written : before.write location value = .ok after) :
    WeakStoreTy roots after := typed.write target valueTyped written

end Goose.Evidence

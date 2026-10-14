import Goose.Proofs.Memory
import Goose.Core.Sound.Store

namespace Goose.Evidence

open Goose.Core Goose.Proofs.Memory

abbrev RootDeclarations := RootInst → Option Ty

def RootDeclarations.Extends (before after : RootDeclarations) : Prop :=
  ∀ root ty, before root = some ty → after root = some ty

def RootDeclarations.Storable (roots : RootDeclarations) : Prop :=
  ∀ root ty, roots root = some ty → ty.storable = true ∨ ty.isRefSlice = true

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

def WeakValueTy (roots : RootDeclarations) (value : Val) : Ty → Prop
  | .ref _ target => ∃ location, value = .ref location ∧ DeclaredLocation roots location target
  | .slice _ element => (∃ location start len arrayTy,
      value = .slice location start len ∧ DeclaredLocation roots location arrayTy ∧
      arrayTy.ownerElem? = some element) ∨
      ∃ location start len count,
        value = .slice location start len ∧ DeclaredLocation roots location (.arr element count)
  | .unit => value = .unit
  | ty => FlatTy ty value

def WeakStoreTy (roots : RootDeclarations) (store : Store) : Prop :=
  ∀ root value, store.roots[root]? = some value →
    ∃ ty, roots root = some ty ∧ WeakValueTy roots value ty

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

theorem WeakValueTy.int {roots : RootDeclarations} {value : Val} {ty : IntTy}
    (typed : WeakValueTy roots value (.int ty)) : ∃ n, value = .int ty n := by
  cases value <;> simp_all [WeakValueTy, FlatTy]

theorem WeakValueTy.ofFlat {roots : RootDeclarations} {value : Val} {ty : Ty}
    (typed : FlatTy ty value) : WeakValueTy roots value ty := by
  cases ty <;> try exact typed
  all_goals cases value <;> simp_all [FlatTy]

theorem WeakValueTy.flat {roots : RootDeclarations} {value : Val} {ty : Ty}
    (flat : ty.flat = true) (typed : WeakValueTy roots value ty) : FlatTy ty value := by
  cases ty <;> try exact typed
  all_goals simp [Ty.flat] at flat

theorem WeakValueTy.ownerFlat {roots : RootDeclarations} {value : Val} {ty element : Ty}
    (owner : ty.ownerElem? = some element) (typed : WeakValueTy roots value ty) : FlatTy ty value := by
  cases ty <;> try exact typed
  all_goals simp [Ty.ownerElem?] at owner

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

theorem WeakValueTy.mono {before after : RootDeclarations} {value : Val} {ty : Ty}
    (extension : before.Extends after) (typed : WeakValueTy before value ty) :
    WeakValueTy after value ty := by
  cases ty with
  | ref permission target =>
    obtain ⟨location, same, declared⟩ := typed
    exact ⟨location, same, declared.mono extension⟩
  | slice permission element =>
    rcases typed with ⟨location, start, len, arrayTy, same, declared, elementType⟩ |
      ⟨location, start, len, count, same, declared⟩
    · exact Or.inl ⟨location, start, len, arrayTy, same, declared.mono extension, elementType⟩
    · exact Or.inr ⟨location, start, len, count, same, declared.mono extension⟩
  | _ => exact typed

theorem WeakStoreTy.mono {before after : RootDeclarations} {store : Store}
    (extension : before.Extends after) (typed : WeakStoreTy before store) :
    WeakStoreTy after store := by
  intro root value present
  obtain ⟨ty, declaration, valueTyped⟩ := typed root value present
  exact ⟨ty, extension _ _ declaration, valueTyped.mono extension⟩

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

theorem WeakValueTy.get {roots : RootDeclarations} {rootTy result : Ty}
    {path : List Nat} {value selected : Val}
    (declared : StoragePath rootTy path result) (typed : WeakValueTy roots value rootTy)
    (read : value.get? path = some selected) : WeakValueTy roots selected result := by
  cases declared with
  | root =>
    simp only [Val.get?, Option.some.injEq] at read
    subst selected
    exact typed
  | fixed tail => exact .ofFlat (StoragePath.get (.fixed tail) typed read)
  | grow tail => exact .ofFlat (StoragePath.get (.grow tail) typed read)
  | shrink tail => exact .ofFlat (StoragePath.get (.shrink tail) typed read)
  | limited tail => exact .ofFlat (StoragePath.get (.limited tail) typed read)
  | field selector tail => exact .ofFlat (StoragePath.get (.field selector tail) typed read)

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

theorem WeakStoreTy.release {roots : RootDeclarations} {store : Store} {root : RootInst}
    (typed : WeakStoreTy roots store) : WeakStoreTy roots (store.release root) := by
  intro other value present
  simp only [Store.release, Std.HashMap.getElem?_erase] at present
  split at present
  · contradiction
  · exact typed other value present

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

theorem WeakStoreTy.flatStep {roots : RootDeclarations} {before after : Store}
    (declarations : roots.Storable) (typed : WeakStoreTy roots before)
    (transition : Goose.Core.Sound.FlatStep before after) : WeakStoreTy roots after := by
  intro root value present
  have oldPresent : before.roots[root]? ≠ none := by
    rcases transition.back root value present with old | changed
    · simp [old]
    · exact changed.2
  cases old : before.roots[root]? with
  | none => exact False.elim (oldPresent old)
  | some oldValue =>
    obtain ⟨ty, declared, valueTyped⟩ := typed root oldValue old
    refine ⟨ty, declared, ?_⟩
    have usable := declarations root ty declared
    have flatTransfer (flatTyped : FlatTy ty oldValue) : WeakValueTy roots value ty := by
      have locationTyped : LocTy before ⟨root, []⟩ ty :=
        ⟨oldValue, (read_ok_iff _ _ _).mpr ⟨oldValue, old, rfl⟩, flatTyped⟩
      obtain ⟨newValue, read, newTyped⟩ := locationTyped.mono transition.le
      obtain ⟨rootValue, newPresent, rootRead⟩ := (read_ok_iff _ _ _).mp read
      rw [present] at newPresent
      cases newPresent
      simp only [Val.get?, Option.some.injEq] at rootRead
      subst newValue
      exact .ofFlat newTyped
    cases ty with
    | unit => simp [Ty.storable, Ty.isRefSlice] at usable
    | ref permission target =>
      obtain ⟨location, same, declaredLocation⟩ := valueTyped
      have kept := transition.keep root oldValue old (by rw [same]; trivial)
      rw [present] at kept
      cases kept
      exact ⟨location, same, declaredLocation⟩
    | slice permission element =>
      have isRef : Goose.Core.Sound.IsRef oldValue := by
        rcases valueTyped with ⟨location, start, len, arrayTy, same, rest⟩ |
          ⟨location, start, len, count, same, rest⟩
        all_goals rw [same]; trivial
      have kept := transition.keep root oldValue old isRef
      rw [present] at kept
      cases kept
      exact valueTyped
    | _ => exact flatTransfer valueTyped

theorem WeakStoreTy.writeFlat {roots : RootDeclarations} {before after : Store}
    {location : Loc} {value : Val} {ty : Ty}
    (declarations : roots.Storable) (typed : WeakStoreTy roots before)
    (target : DeclaredLocation roots location ty) (flat : ty.flat = true)
    (valueTyped : WeakValueTy roots value ty) (written : before.write location value = .ok after) :
    WeakStoreTy roots after := by
  obtain ⟨old, selected, new, rebuilt, rootPresent, oldRead, replaced, modified, roots⟩ :=
    modify_spec before after location (fun _ => some value) written
  have read : before.read location = .ok selected :=
    (read_ok_iff _ _ _).mpr ⟨old, rootPresent, oldRead⟩
  have selectedTyped := (typed.read target read).flat flat
  exact typed.flatStep declarations (Goose.Core.Sound.write_flatStep before after location value ty
    flat ⟨selected, read, selectedTyped⟩ (valueTyped.flat flat) written)

theorem WeakStoreTy.appendOwner {roots : RootDeclarations} {before after : Store}
    {location : Loc} {values : Array Val} {owner element : Ty} {index : Nat}
    (declarations : roots.Storable) (typed : WeakStoreTy roots before)
    (target : DeclaredLocation roots location owner) (ownerType : owner.ownerElem? = some element)
    (flat : element.flat = true)
    (valuesTyped : ∀ (i : Nat) (value : Val), values[i]? = some value → WeakValueTy roots value element)
    (appended : before.append location values = .ok (after, index)) : WeakStoreTy roots after := by
  have successfulRead : ∃ selected, before.read location = .ok selected := by
    rcases append_spec before after location values index appended with
      ⟨elementTy, elements, read, rest⟩ | ⟨elementTy, capacity, slots, len, read, rest⟩
    · exact ⟨_, read⟩
    · exact ⟨_, read⟩
  obtain ⟨selected, read⟩ := successfulRead
  have selectedTyped := (typed.read target read).ownerFlat ownerType
  exact typed.flatStep declarations (Goose.Core.Sound.append_flatStep_owner before after location
    values index owner element ownerType flat ⟨selected, read, selectedTyped⟩
    (fun i value present => (valuesTyped i value present).flat flat) appended)

end Goose.Evidence

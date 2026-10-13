import Goose.Core.Sound.Basic

/-!
Small physical-memory preservation facts used by mutation proofs.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

private theorem fields_flat_get {ts : TyList} {vs : List Val}
    (hflat : ts.flat = true) (hfields : FieldsTy ts vs) :
    ∀ (i : Nat) (x : Val), vs[i]? = some x →
      ∃ t, ts.toList[i]? = some t ∧ t.flat = true ∧ FlatTy t x := by
  intro i
  induction i generalizing ts vs with
  | zero =>
    intro x hget
    cases ts with
    | nil => cases vs <;> simp [TyList.flat, FieldsTy] at hflat hfields hget
    | cons head tail =>
      cases vs with
      | nil => simp [FieldsTy] at hfields
      | cons value values =>
        simp only [TyList.flat, Bool.and_eq_true] at hflat
        simp only [FieldsTy] at hfields
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
        subst x
        exact ⟨head, by simp [TyList.toList], hflat.1, hfields.1⟩
  | succ i ih =>
    intro x hget
    cases ts with
    | nil => cases vs <;> simp [TyList.flat, FieldsTy] at hflat hfields hget
    | cons head tail =>
      cases vs with
      | nil => simp [FieldsTy] at hfields
      | cons value values =>
        simp only [TyList.flat, Bool.and_eq_true] at hflat
        simp only [FieldsTy] at hfields
        simp only [List.getElem?_cons_succ] at hget
        obtain ⟨t, htype, htypeFlat, hvalueFlat⟩ := ih hflat.2 hfields.2 x hget
        exact ⟨t, by simpa [TyList.toList] using htype, htypeFlat, hvalueFlat⟩

private theorem FlatTy.get_flat {T : Ty} {v w : Val} {path : List Nat}
    (hTflat : T.flat = true) (hvalue : FlatTy T v)
    (hget : v.get? path = some w) : ∃ U, U.flat = true ∧ FlatTy U w := by
  induction path generalizing T v w with
  | nil =>
    simp only [get_nil, Option.some.injEq] at hget
    subst w
    exact ⟨T, hTflat, hvalue⟩
  | cons i path ih =>
    cases T with
    | int t => cases v <;> simp [Ty.flat, FlatTy, Val.get?, Val.children?, Val.elems?] at hTflat hvalue hget
    | bool => cases v <;> simp [Ty.flat, FlatTy, Val.get?, Val.children?, Val.elems?] at hTflat hvalue hget
    | arr element count =>
      cases v with
      | fixed values =>
        simp only [FlatTy] at hvalue
        cases hindex : values[i]? with
        | none => simp [Val.get?, Val.children?, Val.elems?, hindex] at hget
        | some x =>
          have htail : x.get? path = some w := by
            simpa [Val.get?, Val.children?, Val.elems?, hindex] using hget
          exact ih (by simpa [Ty.flat] using hTflat) (hvalue.2 i x hindex) htail
      | _ => simp [FlatTy] at hvalue
    | structT sid fields =>
      cases v with
      | record sid' values =>
        simp only [FlatTy] at hvalue
        cases hindex : values[i]? with
        | none => simp [Val.get?, Val.children?, hindex] at hget
        | some x =>
          have htail : x.get? path = some w := by
            simpa [Val.get?, Val.children?, hindex] using hget
          have hlistIndex : values.toList[i]? = some x := by
            simpa only [Array.getElem?_toList] using hindex
          obtain ⟨field, _, hfieldFlat, hfieldValue⟩ :=
            fields_flat_get (by simpa [Ty.flat] using hTflat) hvalue.2 i x hlistIndex
          exact ih hfieldFlat hfieldValue htail
      | _ => simp [FlatTy] at hvalue
    | unit => simp [Ty.flat] at hTflat
    | ref mutability target => simp [Ty.flat] at hTflat
    | slice mutability element => simp [Ty.flat] at hTflat
    | tuple parts => simp [Ty.flat] at hTflat
    | grow element => simp [Ty.flat] at hTflat
    | growshrink element => simp [Ty.flat] at hTflat
    | limited element capacity => simp [Ty.flat] at hTflat

private theorem flatTy_ne_limited_of_flat_type {T element : Ty} {capacity : Nat} {v : Val}
    (hflat : T.flat = true) (hT : FlatTy T v)
    (hlimited : FlatTy (.limited element capacity) v) : False := by
  cases T <;> cases v <;> simp [Ty.flat, FlatTy] at hflat hT hlimited

private theorem growshrink_root_no_limited_path {s : Store} {root : RootInst}
    {path : List Nat} {ownerElement element : Ty} {capacity : Nat}
    (hownerFlat : ownerElement.flat = true)
    (howner : LocTy s ⟨root, []⟩ (.growshrink ownerElement))
    (hlimited : LocTy s ⟨root, path⟩ (.limited element capacity)) : False := by
  obtain ⟨ownerValue, hownerRead, hownerType⟩ := howner
  obtain ⟨limitedValue, hlimitedRead, hlimitedType⟩ := hlimited
  obtain ⟨rootValue, hroot, hownerGet⟩ := (read_ok_iff _ _ _).1 hownerRead
  rw [get_nil] at hownerGet
  cases hownerGet
  obtain ⟨limitedRoot, hlimitedRoot, hlimitedGet⟩ := (read_ok_iff _ _ _).1 hlimitedRead
  rw [hroot] at hlimitedRoot
  cases hlimitedRoot
  cases path with
  | nil =>
    simp only [get_nil, Option.some.injEq] at hlimitedGet
    subst limitedValue
    cases ownerValue <;> simp [FlatTy] at hownerType hlimitedType
  | cons index suffix =>
    cases ownerValue with
    | resizable storedElement values =>
      simp only [FlatTy] at hownerType
      rcases hownerType with ⟨rfl, hitems⟩
      have hget' : (values[index]?).bind (fun value => value.get? suffix) =
          some limitedValue := by
        simpa [get_resizable] using hlimitedGet
      obtain ⟨value, hindex, htail⟩ := Option.bind_eq_some_iff.mp hget'
      obtain ⟨flatType, htypeFlat, hvalueFlat⟩ :=
        FlatTy.get_flat hownerFlat (hitems index value hindex) htail
      exact flatTy_ne_limited_of_flat_type htypeFlat hvalueFlat hlimitedType
    | _ => simp [FlatTy] at hownerType

/-- A limited truncation changes its visible length but preserves every
physical run because its written slots remain in the store. -/
theorem SliceTy.truncate_limited {s s' : Store} {o l : Loc}
    {len start count : Nat} {ownerElement element : Ty} {capacity : Nat}
    (howner : LocTy s o (.limited ownerElement capacity))
    (htruncate : s.truncate o len = .ok s')
    (hslice : SliceTy s l start count element) :
    SliceTy s' l start count element := by
  exact SliceTy.mono
    (truncate_limited_le s s' o len ownerElement capacity howner htruncate).1 hslice

/-- A physical run in a limited array survives shrinking a growshrink owner.
The owner is a whole-root header; if both locations share that root, its flat
element type rules out a limited array anywhere below the resizable header. -/
theorem SliceTy.truncate_growshrink_limited {s s' : Store} {o l : Loc}
    {len start count : Nat} {ownerElement element : Ty} {capacity : Nat}
    (hownerPath : o.path = []) (hownerFlat : ownerElement.flat = true)
    (howner : LocTy s o (.growshrink ownerElement))
    (hlimited : LocTy s l (.limited element capacity))
    (htruncate : s.truncate o len = .ok s')
    (hslice : SliceTy s l start count element) :
    SliceTy s' l start count element := by
  cases o with
  | mk ownerRoot ownerPath =>
    change ownerPath = [] at hownerPath
    subst ownerPath
    cases l with
    | mk sampledRoot sampledPath =>
      by_cases hroot : sampledRoot = ownerRoot
      · subst sampledRoot
        exact False.elim (growshrink_root_no_limited_path hownerFlat howner hlimited)
      · obtain ⟨value, elements, hread, helements, hbounds, hkind⟩ := hslice
        have hagree := truncate_except_owner s s' ⟨ownerRoot, []⟩ len htruncate
        have hread' : s'.read ⟨sampledRoot, sampledPath⟩ = .ok value := by
          rw [read_ok_iff]
          obtain ⟨rootValue, hrootValue, hget⟩ := (read_ok_iff _ _ _).1 hread
          have hunchanged : s'.roots[sampledRoot]? = s.roots[sampledRoot]? := hagree sampledRoot hroot
          exact ⟨rootValue, by rw [hunchanged]; exact hrootValue, hget⟩
        exact ⟨value, elements, hread', helements, hbounds, hkind⟩

end Goose.Core.Sound

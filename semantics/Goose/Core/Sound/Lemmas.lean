import Goose.Core.Sound.Spec

/-!
The store accessors of the evaluator on typed locations, and small facts
about types and runs that several cases of the induction share.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

/-! ### Types -/

theorem flat_refTarget {t : Ty} (h : t.flat = true) : t.refTarget = true := by
  cases t <;> simp_all [Ty.flat, Ty.refTarget]

theorem readable_flat {t : Ty} (h1 : t.readable = true) (h2 : t.refTarget = true) : t.flat = true := by
  cases t <;> simp_all [Ty.flat, Ty.refTarget, Ty.readable]

theorem refTarget_not_refLike {t : Ty} (h : t.refTarget = true) : t.isRefLike = false := by
  cases t <;> simp_all [Ty.refTarget, Ty.isRefLike]

theorem storable_refTarget {t : Ty} (h : t.storable = true) (h2 : t.isRefLike = false) :
    t.refTarget = true := by
  cases t <;> simp_all [Ty.storable, Ty.refTarget, Ty.isRefLike]

theorem flat_no_targets {T : Ty} {v : Val} (h : FlatTy T v) {P : RootInst → Prop} :
    ∀ r, Targets v r → P r :=
  fun _ ht => absurd ht.isRef (flat_not_ref h)

theorem hasTy_no_targets {m : Module} {G : Nat} {s : Store} {v : Val} {T : Ty}
    (h : HasTy m G s v T) (hT : T.isRefLike = false) {P : RootInst → Prop} :
    ∀ r, Targets v r → P r :=
  fun _ ht => absurd ht.isRef (h.not_ref hT)

/-- A value of a type may be passed where the parameter's type differs at most
in mutability. -/
theorem hasTy_passable {m : Module} {G : Nat} {s : Store} {v : Val} {a p : Ty}
    (h : HasTy m G s v a) (hp : a.passableTo p = true) : HasTy m G s v p := by
  cases a <;> cases p <;> simp only [Ty.passableTo, Bool.and_eq_true, beq_iff_eq] at hp <;>
    first
    | (simp at hp; done)
    | (obtain ⟨rfl, _⟩ := hp; exact h)
    | (cases hp; exact h)
    | (injection hp with h1 h2; subst h1; first | (subst h2; exact h) | exact h)
    | exact h

theorem hasTy_nonref_flat {m : Module} {G : Nat} {s : Store} {v : Val} {T : Ty}
    (h : HasTy m G s v T) (h1 : T.storable = true) (h2 : T.isRefLike = false) : FlatTy T v := by
  cases T <;> simp only [Ty.storable, Ty.isRefLike] at h1 h2 <;> first | exact h | cases h1 | cases h2

/-! ### Locations -/

theorem locTy_root {s : Store} {r : RootInst} {v : Val} {T : Ty} (hv : s.roots[r]? = some v)
    (h : FlatTy T v) : LocTy s ⟨r, []⟩ T :=
  ⟨v, (read_ok_iff _ _ _).2 ⟨v, hv, get_nil v⟩, h⟩

theorem read_root {s : Store} {r : RootInst} {v : Val} (hv : s.roots[r]? = some v) :
    s.read ⟨r, []⟩ = .ok v :=
  (read_ok_iff _ _ _).2 ⟨v, hv, get_nil v⟩

/-- The element of a run inside a typed array is a typed location. -/
theorem sliceTy_elem {s : Store} {l : Loc} {st n i : Nat} {E : Ty} (h : SliceTy s l st n E)
    (hi : i < n) : LocTy s ⟨l.root, l.path ++ [st + i]⟩ E := by
  obtain ⟨v, es, hr, hes, hn, hT⟩ := h
  obtain ⟨old, ho, hg⟩ := (read_ok_iff _ _ _).1 hr
  have hlt : st + i < es.size := by omega
  have hread : ∀ e, es[st + i]? = some e → (⟨l.root, l.path ++ [st + i]⟩ : Loc) = ⟨l.root, l.path ++ [st + i]⟩ →
      s.read ⟨l.root, l.path ++ [st + i]⟩ = .ok e := by
    intro e he _
    refine (read_ok_iff _ _ _).2 ⟨old, ho, ?_⟩
    show old.get? (l.path ++ [st + i]) = some e
    rw [get_append, hg]
    simp only [Option.bind_some]
    cases v <;> simp only [Val.elems?, Option.some.injEq, reduceCtorEq] at hes
    · subst hes; rw [get_fixed, he]; simp [get_nil]
    · subst hes; rw [get_resizable, he]; simp [get_nil]
  have he : es[st + i]? = some es[st + i] := Array.getElem?_eq_getElem hlt
  refine ⟨es[st + i], hread _ he rfl, ?_⟩
  rcases hT with hT | ⟨k, hT⟩
  · cases v <;> simp only [FlatTy] at hT
    simp only [Val.elems?, Option.some.injEq] at hes
    subst hes
    exact hT.2 _ _ he
  · cases v <;> simp only [FlatTy] at hT
    simp only [Val.elems?, Option.some.injEq] at hes
    subst hes
    exact hT.2 _ _ he

theorem SliceTy.sub {s : Store} {l : Loc} {st n st' n' : Nat} {E : Ty} (h : SliceTy s l st n E)
    (hb : st' + n' ≤ st + n) : SliceTy s l st' n' E := by
  obtain ⟨v, es, hr, hes, hn, hT⟩ := h
  exact ⟨v, es, hr, hes, by omega, hT⟩

/-- A typed array location is a run over all its elements. -/
theorem sliceTy_of_arr {s : Store} {l : Loc} {E : Ty} {k : Nat} (h : LocTy s l (.arr E k)) :
    SliceTy s l 0 k E := by
  obtain ⟨v, hr, hT⟩ := h
  cases v <;> simp only [FlatTy] at hT
  rename_i es
  exact ⟨_, es, hr, rfl, by omega, Or.inr ⟨k, by simpa [FlatTy] using hT⟩⟩

theorem sliceTy_of_grow {s : Store} {l : Loc} {E : Ty} {es : Array Val} {E' : Ty}
    (h : LocTy s l (.grow E)) (hr : s.read l = .ok (.resizable E' es)) :
    SliceTy s l 0 es.size E := by
  obtain ⟨v, hr', hT⟩ := h
  rw [hr] at hr'; cases hr'
  exact ⟨_, es, hr, rfl, by omega, Or.inl hT⟩

/-! ### Store accessors -/

theorem sat_readLoc {l : Loc} {T : Ty} {s : St} {Q : Val → St → Prop} (h : LocTy s.store l T)
    (k : ∀ v, s.store.read l = .ok v → FlatTy T v → Q v s) : Sat (readLoc l) s Q := by
  obtain ⟨v, hv, hT⟩ := h
  simp only [Sat, readLoc, hv]
  exact k v hv hT

theorem sat_readLoc_bind {l : Loc} {T : Ty} {s : St} {f : Val → M α} {Q : α → St → Prop}
    (h : LocTy s.store l T)
    (k : ∀ v, s.store.read l = .ok v → FlatTy T v → Sat (f v) s Q) : Sat (readLoc l >>= f) s Q := by
  obtain ⟨v, hv, hT⟩ := h
  have e : (readLoc l >>= f) s = f v s := by
    show M.bind' (readLoc l) f s = f v s
    simp [M.bind', readLoc, hv]
  unfold Sat; rw [e]; exact k v hv hT

theorem sat_readRoot {r : RootInst} {v : Val} {s : St} {Q : Val → St → Prop}
    (h : s.store.roots[r]? = some v) (k : Q v s) : Sat (readLoc ⟨r, []⟩) s Q := by
  simp only [Sat, readLoc, read_root h]
  exact k

theorem sat_writeLoc_bind {l : Loc} {v : Val} {T : Ty} {s : St} {f : Unit → M α} {Q : α → St → Prop}
    (h : LocTy s.store l T)
    (k : ∀ st', s.store.write l v = .ok st' → Sat (f ()) { s with store := st' } Q) :
    Sat (writeLoc l v >>= f) s Q := by
  obtain ⟨st', hw⟩ := write_total s.store l v T h
  have e : (writeLoc l v >>= f) s = f () { s with store := st' } := by
    show M.bind' (writeLoc l v) f s = _
    simp [M.bind', writeLoc, hw]
  unfold Sat; rw [e]; exact k st' hw

theorem sat_writeRoot_bind {r : RootInst} {old v : Val} {s : St} {f : Unit → M α} {Q : α → St → Prop}
    (h : s.store.roots[r]? = some old)
    (k : Sat (f ()) { s with store := ⟨(s.store.roots.erase r).insert r v⟩ } Q) :
    Sat (writeLoc ⟨r, []⟩ v >>= f) s Q := by
  have e : (writeLoc ⟨r, []⟩ v >>= f) s = f () { s with store := ⟨(s.store.roots.erase r).insert r v⟩ } := by
    show M.bind' (writeLoc ⟨r, []⟩ v) f s = _
    simp [M.bind', writeLoc, write_root s.store r old v h]
  unfold Sat; rw [e]; exact k

theorem sat_appendLoc_bind {l : Loc} {vs : Array Val} {E : Ty} {s : St} {f : Nat → M α}
    {Q : α → St → Prop} (h : LocTy s.store l (.grow E))
    (k : ∀ st' i, s.store.append l vs = .ok (st', i) → Sat (f i) { s with store := st' } Q) :
    Sat (appendLoc l vs >>= f) s Q := by
  obtain ⟨st', i, hw⟩ := append_total s.store l vs E h
  have e : (appendLoc l vs >>= f) s = f i { s with store := st' } := by
    show M.bind' (appendLoc l vs) f s = _
    simp [M.bind', appendLoc, hw]
  unfold Sat; rw [e]; exact k st' i hw

theorem sat_lengthLoc_bind {l : Loc} {E : Ty} {s : St} {f : Nat → M α} {Q : α → St → Prop}
    (h : LocTy s.store l (.grow E))
    (k : ∀ es, s.store.read l = .ok (.resizable E es) → Sat (f es.size) s Q) :
    Sat (lengthLoc l >>= f) s Q := by
  obtain ⟨v, hv, hT⟩ := h
  rcases v with _|_|_|_|⟨E', es⟩|_|_ <;> simp only [FlatTy] at hT
  obtain ⟨rfl, _⟩ := hT
  have e : (lengthLoc l >>= f) s = f es.size s := by
    show M.bind' (lengthLoc l) f s = _
    simp [M.bind', lengthLoc, Store.length, hv]
  unfold Sat; rw [e]; exact k es hv

@[simp] theorem sat_bindRoot_bind {r : RootInst} {v : Val} {s : St} {f : Unit → M α} {Q : α → St → Prop} :
    Sat (bindRoot r v >>= f) s Q ↔ Sat (f ()) { s with store := s.store.introduce r v } Q := Iff.rfl

@[simp] theorem sat_freshScope_bind {s : St} {f : ScopeInst → M α} {Q : α → St → Prop} :
    Sat (freshScope >>= f) s Q ↔ Sat (f s.nextScope) { s with nextScope := s.nextScope + 1 } Q := Iff.rfl

@[simp] theorem sat_freshAct_bind {s : St} {f : ActId → M α} {Q : α → St → Prop} :
    Sat (freshAct >>= f) s Q ↔ Sat (f s.nextAct) { s with nextAct := s.nextAct + 1 } Q := Iff.rfl

@[simp] theorem sat_emit_bind {t : String} {s : St} {f : Unit → M α} {Q : α → St → Prop} :
    Sat (emit t >>= f) s Q ↔ Sat (f ()) { s with trace := s.trace ++ t } Q := Iff.rfl

@[simp] theorem sat_fault_iff {k : FaultKind} {s : St} {Q : α → St → Prop} :
    Sat (fault k : M α) s Q ↔ False := Iff.rfl

end Goose.Core.Sound

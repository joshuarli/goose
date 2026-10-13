import Goose.Core.Validate
import Goose.Core.Eval
import Goose.Proofs.Memory

/-!
Vocabulary of the safety proof: what it means for a computation of the
evaluator not to fault, for a value to have a type in a store, and for a store
to change without invalidating what was typed in it.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

/-! ### Computations that do not fault -/

/-- The computation, run from `s`, does not fault, and a result it yields
satisfies `Q`. Aborts, exits and running out of fuel are allowed. -/
def Sat (m : M α) (s : St) (Q : α → St → Prop) : Prop :=
  match m s with
  | .ok a s' => Q a s'
  | .stop (.fault _) _ => False
  | .stop _ _ => True

theorem Sat.bind {m : M α} {f : α → M β} {s : St} {R : α → St → Prop} {Q : β → St → Prop}
    (h1 : Sat m s R) (h2 : ∀ a s', R a s' → Sat (f a) s' Q) : Sat (m >>= f) s Q := by
  show Sat (M.bind' m f) s Q
  unfold Sat M.bind' at *
  cases hr : m s with
  | ok a s1 => rw [hr] at h1; exact h2 a s1 h1
  | stop e s1 =>
    rw [hr] at h1
    cases e <;> simp_all

/-- As `Sat.bind`, with the first computation's result in hand. -/
theorem Sat.bind_eq {m : M α} {f : α → M β} {s : St} {R : α → St → Prop} {Q : β → St → Prop}
    (h1 : Sat m s R) (h2 : ∀ a s', m s = .ok a s' → R a s' → Sat (f a) s' Q) : Sat (m >>= f) s Q := by
  show Sat (M.bind' m f) s Q
  unfold Sat M.bind' at *
  cases hr : m s with
  | ok a s1 => rw [hr] at h1; exact h2 a s1 hr h1
  | stop e s1 =>
    rw [hr] at h1
    cases e <;> simp_all

theorem Sat.mono {m : M α} {s : St} {R Q : α → St → Prop}
    (h1 : Sat m s R) (h2 : ∀ a s', R a s' → Q a s') : Sat m s Q := by
  unfold Sat at *
  cases hr : m s with
  | ok a s1 => rw [hr] at h1; exact h2 a s1 h1
  | stop e s1 => rw [hr] at h1; cases e <;> simp_all

@[simp] theorem sat_pure {a : α} {s : St} {Q : α → St → Prop} : Sat (pure a) s Q ↔ Q a s := Iff.rfl

@[simp] theorem sat_pure_bind {a : α} {f : α → M β} {s : St} {Q : β → St → Prop} :
    Sat (pure a >>= f) s Q ↔ Sat (f a) s Q := Iff.rfl

@[simp] theorem sat_abort {k : AbortKind} {o : OriginId} {s : St} {Q : α → St → Prop} :
    Sat (abortAt k o) s Q ↔ True := Iff.rfl

@[simp] theorem sat_timeout {s : St} {Q : α → St → Prop} : Sat (timeout : M α) s Q ↔ True := Iff.rfl

@[simp] theorem sat_stop_exit {c : Int} {s : St} {Q : α → St → Prop} :
    Sat (M.stop (.exit c) : M α) s Q ↔ True := Iff.rfl

@[simp] theorem sat_abort_bind {k : AbortKind} {o : OriginId} {f : α → M β} {s : St}
    {Q : β → St → Prop} : Sat (abortAt k o >>= f) s Q ↔ True := Iff.rfl

@[simp] theorem sat_timeout_bind {f : α → M β} {s : St} {Q : β → St → Prop} :
    Sat ((timeout : M α) >>= f) s Q ↔ True := Iff.rfl

theorem sat_ite {c : Prop} [Decidable c] {t e : M α} {s : St} {Q : α → St → Prop}
    (ht : c → Sat t s Q) (he : ¬ c → Sat e s Q) : Sat (if c then t else e) s Q := by
  by_cases h : c <;> simp [h, ht, he]

/-! ### Values, types and what a reference targets -/

def IsRef : Val → Prop
  | .ref _ => True
  | .slice _ _ _ => True
  | _ => False

/-- The root a reference or slice points into. -/
def Targets : Val → RootInst → Prop
  | .ref l, r => l.root = r
  | .slice l _ _, r => l.root = r
  | _, _ => False

theorem Targets.isRef {v : Val} {r : RootInst} (h : Targets v r) : IsRef v := by
  cases v <;> simp_all [Targets, IsRef]

/-- A reference to a whole global that is not initialized yet. Such a reference
may be made and passed while earlier globals are initialized, but not used. -/
def Unbound (m : Module) (G : Nat) (l : Loc) (T : Ty) : Prop :=
  ∃ g gl, G ≤ g ∧ l.root = .global g ∧ m.globals[g]? = some gl ∧ FieldPath gl.ty l.path T

def LocOk (m : Module) (G : Nat) (s : Store) (l : Loc) (T : Ty) : Prop :=
  LocTy s l T ∨ Unbound m G l T

/-- A location for an owner denotes its header, never an element path. -/
def HeaderLoc (l : Loc) (T : Ty) : Prop :=
  T.ownerElem?.isSome → l.path = []

theorem HeaderLoc.root {r : RootInst} {T : Ty} : HeaderLoc ⟨r, []⟩ T := by
  intro _
  rfl

theorem HeaderLoc.ofFlat {l : Loc} {T : Ty} (hflat : T.flat = true) : HeaderLoc l T := by
  intro howner
  cases T <;> simp [Ty.flat, Ty.ownerElem?] at hflat howner

theorem LocOk.fieldPath {m : Module} {G : Nat} {s : Store} {l : Loc} {a b : Ty} {p : List Nat}
    (h : LocOk m G s l a) (k : FieldPath a p b) : LocOk m G s ⟨l.root, l.path ++ p⟩ b := by
  rcases h with h | ⟨g, gl, hG, hr, hg, hp⟩
  · exact Or.inl (h.fieldPath k)
  · exact Or.inr ⟨g, gl, hG, hr, hg, hp.append k⟩

/-- A run of `n` elements from `st` inside the array of `E` at `l`. -/
def SliceTy (s : Store) (l : Loc) (st n : Nat) (E : Ty) : Prop :=
  ∃ v es, s.read l = .ok v ∧ v.elems? = some es ∧ st + n ≤ es.size ∧
    (FlatTy (.grow E) v ∨ FlatTy (.growshrink E) v ∨
      (∃ k, FlatTy (.arr E k) v) ∨ (∃ capacity, FlatTy (.limited E capacity) v))

/-- The value has the type in the store. Mutability is not part of it. -/
def HasTy (m : Module) (G : Nat) (s : Store) (v : Val) : Ty → Prop
  | .ref _ T => ∃ l, v = .ref l ∧ ((T.refTarget = true ∧ LocOk m G s l T ∧ HeaderLoc l T) ∨
      (T.isSlice = true ∧ l.path = [] ∧ s.roots[l.root]? ≠ none))
  | .slice _ E => ∃ l st n, v = .slice l st n ∧ E.flat = true ∧ SliceTy s l st n E
  | .unit => v = .unit
  | .tuple _ => False
  | .int t => FlatTy (.int t) v
  | .bool => FlatTy .bool v
  | .arr E k => FlatTy (.arr E k) v
  | .grow E => FlatTy (.grow E) v
  | .growshrink E => FlatTy (.growshrink E) v
  | .limited E capacity => FlatTy (.limited E capacity) v
  | .structT sid ts => FlatTy (.structT sid ts) v

theorem HasTy.isRef {m : Module} {G : Nat} {s : Store} {v : Val} {T : Ty}
    (h : HasTy m G s v T) (hT : T.isRefLike = true) : IsRef v := by
  cases T <;> simp only [Ty.isRefLike] at hT <;> try cases hT
  · obtain ⟨l, rfl, _⟩ := h; trivial
  · obtain ⟨l, a, b, rfl, _⟩ := h; trivial

/-- A typed non-reference root exposes its stored value with its declared type. -/
theorem LocTy.hasTyRoot {m : Module} {G : Nat} {s : Store} {r : RootInst} {T : Ty}
    (h : LocTy s ⟨r, []⟩ T) (hnonref : T.isRefLike = false) :
    ∃ v, s.roots[r]? = some v ∧ HasTy m G s v T := by
  obtain ⟨v, hread, hflat⟩ := h
  obtain ⟨root, hroot, hget⟩ := (read_ok_iff _ _ _).1 hread
  rw [get_nil] at hget
  cases hget
  cases T with
  | unit => cases hflat
  | tuple parts => cases hflat
  | ref mu target => simp [Ty.isRefLike] at hnonref
  | slice mu element => simp [Ty.isRefLike] at hnonref
  | int t => exact ⟨v, hroot, hflat⟩
  | bool => exact ⟨v, hroot, hflat⟩
  | arr element count => exact ⟨v, hroot, hflat⟩
  | grow element => exact ⟨v, hroot, hflat⟩
  | growshrink element => exact ⟨v, hroot, hflat⟩
  | limited element capacity => exact ⟨v, hroot, hflat⟩
  | structT id fields => exact ⟨v, hroot, hflat⟩

/-- What a stored reference or slice must denote, whatever its type. -/
def Held (m : Module) (G : Nat) (s : Store) : Val → Prop
  | .ref l => (∃ T, T.refTarget = true ∧ LocOk m G s l T) ∨
      (l.path = [] ∧ s.roots[l.root]? ≠ none)
  | .slice l st n => ∃ E, SliceTy s l st n E
  | _ => True

theorem HasTy.ownerHeader {m : Module} {G : Nat} {s : Store} {l : Loc} {mu : Mutability} {T : Ty}
    (h : HasTy m G s (.ref l) (.ref mu T)) (howner : T.ownerElem?.isSome = true) : l.path = [] := by
  simp only [HasTy] at h
  obtain ⟨l', hv, hloc⟩ := h
  cases hv
  rcases hloc with ⟨_, _, hheader⟩ | ⟨_, hpath, _⟩
  · exact hheader howner
  · exact hpath

/-- A typed reference to an owner cannot target a nonempty path. -/
theorem HasTy.ownerHeader_excludes_nonempty {m : Module} {G : Nat} {s : Store} {l : Loc}
    {mu : Mutability} {T : Ty} (h : HasTy m G s (.ref l) (.ref mu T))
    (howner : T.ownerElem?.isSome = true) (hnonempty : l.path ≠ []) : False := by
  exact hnonempty (h.ownerHeader howner)

theorem dom_mono {s s' : Store} {r : RootInst} (hle : StoreLe s s') (h : s.roots[r]? ≠ none) :
    s'.roots[r]? ≠ none := by
  cases hv : s.roots[r]? with
  | none => exact absurd hv h
  | some v =>
    obtain ⟨v', hv', _⟩ := hle r v hv
    rw [hv']; simp

theorem flat_not_ref {T : Ty} {v : Val} (h : FlatTy T v) : ¬ IsRef v := by
  cases v <;> simp only [IsRef, not_false_eq_true, not_true_eq_false]
  all_goals (cases T <;> simp [FlatTy] at h)

theorem SliceTy.mono {s s' : Store} {l : Loc} {st n : Nat} {E : Ty} (hle : StoreLe s s')
    (h : SliceTy s l st n E) : SliceTy s' l st n E := by
  obtain ⟨v, es, hr, hes, hn, hT⟩ := h
  obtain ⟨old, ho, hg⟩ := (read_ok_iff _ _ _).1 hr
  obtain ⟨old', ho', hr'⟩ := hle _ _ ho
  obtain ⟨x', hx', hT', hs⟩ := hr' _ _ hg
  obtain ⟨es', hes', hle'⟩ := hs es hes
  refine ⟨x', es', (read_ok_iff _ _ _).2 ⟨old', ho', hx'⟩, hes', by omega, ?_⟩
  rcases hT with h | h | ⟨k, h⟩ | ⟨capacity, h⟩
  · exact Or.inl (hT' _ h)
  · exact Or.inr (Or.inl (hT' _ h))
  · exact Or.inr (Or.inr (Or.inl ⟨k, hT' _ h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨capacity, hT' _ h⟩))

theorem LocOk.mono {m : Module} {G : Nat} {s s' : Store} {l : Loc} {T : Ty} (hle : StoreLe s s')
    (h : LocOk m G s l T) : LocOk m G s' l T :=
  h.elim (fun h => Or.inl (LocTy.mono hle h)) Or.inr

/-- Whole-root typing also preserves a declared global that is not initialized
yet: its declaration does not depend on the current store. -/
theorem LocOk.root_mono {m : Module} {G : Nat} {s s' : Store} {r : RootInst} {T : Ty}
    (hle : RootTyLe s s') (h : LocOk m G s ⟨r, []⟩ T) : LocOk m G s' ⟨r, []⟩ T :=
  h.elim (fun ht => Or.inl (hle r T ht)) Or.inr

theorem flat_mono {s s' : Store} {r : RootInst} {T : Ty} {v : Val} (hle : StoreLe s s')
    (hv : s.roots[r]? = some v) (h : FlatTy T v) : ∃ v', s'.roots[r]? = some v' ∧ FlatTy T v' := by
  obtain ⟨v', hv', hr⟩ := hle r v hv
  obtain ⟨x', hx', hT, _⟩ := hr [] v (get_nil v)
  rw [get_nil] at hx'; cases hx'
  exact ⟨v', hv', hT T h⟩

theorem HasTy.mono {m : Module} {G : Nat} {s s' : Store} {v : Val} {T : Ty} (hle : StoreLe s s')
    (h : HasTy m G s v T) : HasTy m G s' v T := by
  cases T <;> simp only [HasTy] at h ⊢ <;> try exact h
  · obtain ⟨l, h1, h2⟩ := h
    exact ⟨l, h1, h2.elim (fun h => Or.inl ⟨h.1, h.2.1.mono hle, h.2.2⟩)
      (fun h => Or.inr ⟨h.1, h.2.1, dom_mono hle h.2.2⟩)⟩
  · obtain ⟨l, st, n, h1, h2, h3⟩ := h; exact ⟨l, st, n, h1, h2, h3.mono hle⟩

/-- Owner references denote whole-root headers, so preserving root types is
enough even when truncation invalidates some interior locations. -/
theorem HasTy.owner_mono {m : Module} {G : Nat} {s s' : Store}
    {l : Loc} {mu : Mutability} {T : Ty}
    (hle : RootTyLe s s') (howner : T.ownerElem?.isSome = true)
    (h : HasTy m G s (.ref l) (.ref mu T)) : HasTy m G s' (.ref l) (.ref mu T) := by
  have hpath := h.ownerHeader howner
  obtain ⟨r, path⟩ := l
  change path = [] at hpath
  subst path
  obtain ⟨l', hv, hloc⟩ := h
  cases hv
  refine ⟨⟨r, []⟩, rfl, ?_⟩
  rcases hloc with ⟨htarget, hloc, hheader⟩ | ⟨hslice, _, _⟩
  · exact Or.inl ⟨htarget, hloc.root_mono hle, hheader⟩
  · cases T <;> simp [Ty.ownerElem?, Ty.isSlice] at howner hslice

theorem Held.mono {m : Module} {G : Nat} {s s' : Store} {v : Val} (hle : StoreLe s s')
    (h : Held m G s v) : Held m G s' v := by
  cases v <;> simp only [Held] at h ⊢
  · exact h.elim (fun ⟨T, h1, h2⟩ => Or.inl ⟨T, h1, h2.mono hle⟩)
      (fun h => Or.inr ⟨h.1, dom_mono hle h.2⟩)
  · obtain ⟨E, h1⟩ := h; exact ⟨E, h1.mono hle⟩

theorem HasTy.held {m : Module} {G : Nat} {s : Store} {v : Val} {T : Ty}
    (h : HasTy m G s v T) : Held m G s v := by
  cases T <;> simp only [HasTy] at h
  case ref _ T =>
    obtain ⟨l, rfl, h2⟩ := h
    exact h2.elim (fun h => Or.inl ⟨T, h.1, h.2.1⟩) (fun h => Or.inr ⟨h.2.1, h.2.2⟩)
  case slice _ E => obtain ⟨l, st, n, rfl, _, h3⟩ := h; exact ⟨E, h3⟩
  case unit => subst h; trivial
  all_goals (cases v <;> simp_all [Held, FlatTy])

/-- A value of a type that is not a reference or slice type targets nothing. -/
theorem HasTy.not_ref {m : Module} {G : Nat} {s : Store} {v : Val} {T : Ty}
    (h : HasTy m G s v T) (hT : T.isRefLike = false) : ¬ IsRef v := by
  cases T <;> simp only [HasTy, Ty.isRefLike] at h hT
  case unit => subst h; simp [IsRef]
  all_goals first | exact flat_not_ref h | cases hT

theorem HasTy.flat {m : Module} {G : Nat} {s : Store} {v : Val} {T : Ty}
    (h : HasTy m G s v T) (hT : T.flat = true) : FlatTy T v := by
  cases T <;> simp only [HasTy, Ty.flat] at h hT <;> first | exact h | cases hT

theorem HasTy.flatOfStorableNonref {m : Module} {G : Nat} {s : Store} {v : Val} {T : Ty}
    (h : HasTy m G s v T) (hstorable : T.storable = true) (hnonref : T.isRefLike = false) :
    FlatTy T v := by
  cases T with
  | int _ => exact h
  | bool => exact h
  | unit => simp [Ty.storable] at hstorable
  | arr _ _ => exact h
  | grow _ => exact h
  | growshrink _ => exact h
  | limited _ _ => exact h
  | ref _ _ => simp [Ty.isRefLike] at hnonref
  | slice _ _ => simp [Ty.isRefLike] at hnonref
  | tuple _ => simp [Ty.storable] at hstorable
  | structT _ _ => exact h

theorem Ty.storable_of_paramOk_nonref {T : Ty} (hparam : T.paramOk = true)
    (hnonref : T.isRefLike = false) : T.storable = true := by
  cases T with
  | int _ => rfl
  | bool => rfl
  | unit => simp [Ty.paramOk, Ty.storable, Ty.isRefSlice] at hparam
  | arr _ _ => simpa [Ty.paramOk, Ty.storable, Ty.isRefSlice] using hparam
  | grow _ => simpa [Ty.paramOk, Ty.storable, Ty.isRefSlice] using hparam
  | growshrink _ => simpa [Ty.paramOk, Ty.storable, Ty.isRefSlice] using hparam
  | limited _ _ => simpa [Ty.paramOk, Ty.storable, Ty.isRefSlice] using hparam
  | ref _ _ => simp [Ty.isRefLike] at hnonref
  | slice _ _ => simp [Ty.isRefLike] at hnonref
  | tuple _ => simp [Ty.paramOk, Ty.storable, Ty.isRefSlice] at hparam
  | structT _ _ => simpa [Ty.paramOk, Ty.storable, Ty.isRefSlice] using hparam

theorem hasTy_of_flat {m : Module} {G : Nat} {s : Store} {v : Val} {T : Ty}
    (h : FlatTy T v) (hT : T.flat = true ∨ ∃ E, T = .grow E) : HasTy m G s v T := by
  cases T <;> simp only [HasTy] <;> try exact h
  all_goals (rcases hT with hT | ⟨E, hT⟩ <;> simp [Ty.flat] at hT)

theorem hasTy_int {m : Module} {G : Nat} {s : Store} {v : Val} {t : IntTy}
    (h : HasTy m G s v (.int t)) : ∃ n, v = .int t n := by
  cases v <;> simp [HasTy, FlatTy] at h
  subst h; exact ⟨_, rfl⟩

theorem hasTy_bool {m : Module} {G : Nat} {s : Store} {v : Val}
    (h : HasTy m G s v .bool) : ∃ b, v = .bool b := by
  cases v <;> simp [HasTy, FlatTy] at h
  exact ⟨_, rfl⟩

end Goose.Core.Sound

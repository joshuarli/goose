import Goose.Core.Sound.Basic

/-!
How each store operation of the evaluator acts on typed locations and on the
references the store holds: writes of flat values, growth, binding a fresh
root, rebinding a reference and releasing a scope.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

theorem get_reinsert (roots : Std.HashMap RootInst Val) (r r' : RootInst) (v : Val) :
    ((roots.erase r).insert r v)[r']? = if r = r' then some v else roots[r']? := by
  by_cases h : r = r' <;> simp [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, h]

theorem get_introduce (s : Store) (r r' : RootInst) (v : Val) :
    (s.introduce r v).roots[r']? = if r = r' then some v else s.roots[r']? := by
  by_cases h : r = r' <;> simp [Store.introduce, Std.HashMap.getElem?_insert, h]

theorem modifyAt_total (f : Val → Option Val) :
    ∀ (p : List Nat) (v x y : Val), v.get? p = some x → f x = some y →
      ∃ v', v.modifyAt? p f = some v' := by
  intro p
  induction p with
  | nil =>
    intro v x y h1 h2
    rw [get_nil] at h1; cases h1
    exact ⟨y, by simp [Val.modifyAt?, h2]⟩
  | cons i rest ih =>
    intro v x y h1 h2
    cases v with
    | fixed es =>
      rw [get_fixed] at h1
      cases hi : es[i]? with
      | none => simp [hi] at h1
      | some e =>
        simp only [hi, Option.bind_some] at h1
        obtain ⟨hlt, he⟩ := Array.getElem?_eq_some_iff.1 hi
        obtain ⟨e', he'⟩ := ih e x y h1 h2
        refine ⟨.fixed (es.set i e'), ?_⟩
        simp only [Val.modifyAt?, hlt, dite_true, he, he']
    | record sid es =>
      rw [get_record] at h1
      cases hi : es[i]? with
      | none => simp [hi] at h1
      | some e =>
        simp only [hi, Option.bind_some] at h1
        obtain ⟨hlt, he⟩ := Array.getElem?_eq_some_iff.1 hi
        obtain ⟨e', he'⟩ := ih e x y h1 h2
        refine ⟨.record sid (es.set i e'), ?_⟩
        simp only [Val.modifyAt?, hlt, dite_true, he, he']
    | resizable E es =>
      rw [get_resizable] at h1
      cases hi : es[i]? with
      | none => simp [hi] at h1
      | some e =>
        simp only [hi, Option.bind_some] at h1
        obtain ⟨hlt, he⟩ := Array.getElem?_eq_some_iff.1 hi
        obtain ⟨e', he'⟩ := ih e x y h1 h2
        refine ⟨.resizable E (es.set i e'), ?_⟩
        simp only [Val.modifyAt?, hlt, dite_true, he, he']
    | _ => simp [Val.get?, Val.children?, Val.elems?] at h1

theorem modify_total (s : Store) (l : Loc) (f : Val → Option Val) (x y : Val)
    (hr : s.read l = .ok x) (hf : f x = some y) : ∃ s', s.modify l f = .ok s' := by
  obtain ⟨old, ho, hg⟩ := (read_ok_iff _ _ _).1 hr
  obtain ⟨new, hn⟩ := modifyAt_total f l.path old x y hg hf
  exact ⟨⟨(s.roots.erase l.root).insert l.root new⟩, by simp [Store.modify, ho, hg, hn]⟩

/-- Rewriting below a root that holds an array, or replacing a value that is
not a reference by another that is not, leaves no reference at the root. -/
theorem modifyAt_notRef (f : Val → Option Val) (p : List Nat) (v v' x : Val)
    (h : v.modifyAt? p f = some v') (hg : v.get? p = some x) (hx : ¬ IsRef x)
    (hy : ∀ y, f x = some y → ¬ IsRef y) : ¬ IsRef v ∧ ¬ IsRef v' := by
  cases p with
  | nil =>
    rw [get_nil] at hg; cases hg
    simp only [Val.modifyAt?] at h
    exact ⟨hx, hy _ h⟩
  | cons i rest =>
    cases v with
    | fixed es =>
      simp only [Val.modifyAt?] at h
      split at h
      · split at h
        · cases h; simp [IsRef]
        · cases h
      · cases h
    | record sid es =>
      simp only [Val.modifyAt?] at h
      split at h
      · split at h
        · cases h; simp [IsRef]
        · cases h
      · cases h
    | resizable E es =>
      simp only [Val.modifyAt?] at h
      split at h
      · split at h
        · cases h; simp [IsRef]
        · cases h
      · cases h
    | _ => simp [Val.modifyAt?] at h

/-- A store step that touches no reference: typed locations stay typed, every
stored reference is kept, and a root that changed holds no reference. -/
structure FlatStep (s s' : Store) : Prop where
  le : StoreLe s s'
  keep : ∀ (r : RootInst) (v : Val), s.roots[r]? = some v → IsRef v → s'.roots[r]? = some v
  back : ∀ (r : RootInst) (v' : Val), s'.roots[r]? = some v' →
    s.roots[r]? = some v' ∨ (¬ IsRef v' ∧ s.roots[r]? ≠ none)

theorem flatStep_modify (s s' : Store) (l : Loc) (f : Val → Option Val) (x : Val)
    (h : s.modify l f = .ok s') (hr : s.read l = .ok x) (hx : ¬ IsRef x)
    (hy : ∀ y, f x = some y → ¬ IsRef y ∧ Refines x y) : FlatStep s s' := by
  obtain ⟨old, x1, y, new, ho, hg, hf, hm, hroots⟩ := modify_spec s s' l f h
  obtain ⟨old2, ho2, hg2⟩ := (read_ok_iff _ _ _).1 hr
  rw [ho] at ho2; cases ho2
  rw [hg] at hg2
  obtain rfl : x1 = x := by simpa using hg2
  have hnr := modifyAt_notRef f l.path old new x1 hm hg hx (fun y hy' => (hy y hy').1)
  refine ⟨?_, ?_, ?_⟩
  · apply modify_le s s' l f h
    intro old' x' y' ho' hx' hy'
    rw [ho] at ho'; cases ho'
    rw [hg] at hx'; cases hx'
    exact (hy y' hy').2
  · intro r v hv href
    have hne : l.root ≠ r := by
      rintro rfl
      rw [ho] at hv; cases hv
      exact hnr.1 href
    rw [hroots, get_reinsert]; simp [hne, hv]
  · intro r v' hv'
    rw [hroots, get_reinsert] at hv'
    by_cases hne : l.root = r
    · subst hne
      simp only [if_true, Option.some.injEq] at hv'
      subst hv'
      exact Or.inr ⟨hnr.2, by simp [ho]⟩
    · simp only [hne, if_false] at hv'
      exact Or.inl hv'

theorem write_total (s : Store) (l : Loc) (v : Val) (T : Ty) (hl : LocTy s l T) :
    ∃ s', s.write l v = .ok s' := by
  obtain ⟨x, hx, _⟩ := hl
  exact modify_total s l _ x v hx rfl

theorem write_flatStep (s s' : Store) (l : Loc) (v : Val) (T : Ty) (hT : T.flat = true)
    (hl : LocTy s l T) (hv : FlatTy T v) (h : s.write l v = .ok s') : FlatStep s s' := by
  obtain ⟨x, hx, hTx⟩ := hl
  refine flatStep_modify s s' l _ x h hx (flat_not_ref hTx) ?_
  intro y hy
  simp only [Option.some.injEq] at hy
  subst hy
  exact ⟨flat_not_ref hv, flat_refines T hT _ _ hTx hv⟩

theorem append_total (s : Store) (l : Loc) (vs : Array Val) (E : Ty) (hl : LocTy s l (.grow E)) :
    ∃ s' n, s.append l vs = .ok (s', n) := by
  obtain ⟨x, hx, hTx⟩ := hl
  rcases x with _|_|_|_|_|⟨E', es⟩|_|_ <;> simp only [FlatTy] at hTx
  obtain ⟨s', hs'⟩ := modify_total s l (Val.appendAll vs) _ _ hx rfl
  exact ⟨s', es.size, by simp [Store.append, Store.length, hx, hs']⟩

theorem append_flatStep (s s' : Store) (l : Loc) (vs : Array Val) (n : Nat) (E : Ty)
    (hl : LocTy s l (.grow E)) (hvs : ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e)
    (h : s.append l vs = .ok (s', n)) : FlatStep s s' := by
  obtain ⟨E1, es, hr, hn, hm⟩ := append_spec s s' l vs n h
  have hE : E = E1 := by
    obtain ⟨x, hx, hT⟩ := hl
    rw [hr] at hx; cases hx
    simpa [FlatTy] using hT.1
  subst hE
  refine flatStep_modify s s' l _ _ hm hr (by simp [IsRef]) ?_
  intro y hy
  simp only [Val.appendAll, Option.some.injEq] at hy
  subst hy
  exact ⟨by simp [IsRef], refines_push E es vs hvs⟩

/-! ### The store invariant -/

/-- The first root does not end before the second: a global, or a local of a
scope instance entered no later. Scope instances end last in, first out. -/
def Older : RootInst → RootInst → Prop
  | .global _, _ => True
  | .local _ s' _, .local _ s _ => s' ≤ s
  | .local _ _ _, .global _ => False

/-- What holds of the whole store between any two steps of a run: every stored
reference or slice denotes a typed location or run, it points into a root that
ends no earlier than its holder, every scope instance in use was handed out,
and the globals initialized so far hold values of their types. -/
structure StoreInv (m : Module) (G : Nat) (s : St) : Prop where
  live : ∀ (r : RootInst) (v : Val), s.store.roots[r]? = some v → Held m G s.store v
  age : ∀ (r : RootInst) (v : Val), s.store.roots[r]? = some v → ∀ r', Targets v r' → Older r' r
  fresh : ∀ (a : ActId) (si : ScopeInst) (x : VarId), s.store.roots[RootInst.local a si x]? ≠ none → si < s.nextScope
  globals : ∀ (g : Nat) (gl : Global), g < G → m.globals[g]? = some gl → LocTy s.store ⟨.global g, []⟩ gl.ty

theorem StoreInv.flatStep {m : Module} {G : Nat} {s : St} {st' : Store}
    (hi : StoreInv m G s) (h : FlatStep s.store st') : StoreInv m G { s with store := st' } := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r v hv
    rcases h.back r v hv with h0 | ⟨hn, _⟩
    · exact (hi.live r v h0).mono h.le
    · cases v <;> simp_all [Held, IsRef]
  · intro r v hv r' ht
    rcases h.back r v hv with h0 | ⟨hn, _⟩
    · exact hi.age r v h0 r' ht
    · exact absurd ht.isRef hn
  · intro a si x hx
    apply hi.fresh a si x
    cases hv : st'.roots[RootInst.local a si x]? with
    | none => exact absurd hv hx
    | some v' =>
      rcases h.back _ v' hv with h0 | ⟨_, h1⟩
      · simp [h0]
      · exact h1
  · intro g gl hg hgl
    exact LocTy.mono h.le (hi.globals g gl hg hgl)

/-- Binding a root that was absent. -/
theorem StoreInv.bind {m : Module} {G : Nat} {s : St} {r : RootInst} {v : Val}
    (hi : StoreInv m G s) (hfree : s.store.roots[r]? = none) (hv : Held m G s.store v)
    (hage : ∀ r', Targets v r' → Older r' r)
    (hfr : ∀ a si x, r = .local a si x → si < s.nextScope) :
    StoreInv m G { s with store := s.store.introduce r v } := by
  have hle := introduce_le s.store r v hfree
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r1 v1 h1
    rw [get_introduce] at h1
    by_cases hr : r = r1
    · simp only [hr, if_true, Option.some.injEq] at h1
      subst h1; exact hv.mono hle
    · simp only [hr, if_false] at h1
      exact (hi.live r1 v1 h1).mono hle
  · intro r1 v1 h1 r' ht
    rw [get_introduce] at h1
    by_cases hr : r = r1
    · simp only [hr, if_true, Option.some.injEq] at h1
      subst h1; subst hr; exact hage r' ht
    · simp only [hr, if_false] at h1
      exact hi.age r1 v1 h1 r' ht
  · intro a si x hx
    rw [get_introduce] at hx
    by_cases hr : r = .local a si x
    · exact hfr a si x hr
    · simp only [hr, if_false] at hx
      exact hi.fresh a si x hx
  · intro g gl hg hgl
    exact LocTy.mono hle (hi.globals g gl hg hgl)

/-- Replacing the reference a root holds by another. -/
theorem rebind_le (s : Store) (r : RootInst) (old v : Val) (ho : s.roots[r]? = some old)
    (hold : IsRef old) : StoreLe s ⟨(s.roots.erase r).insert r v⟩ := by
  intro r1 v1 h1
  by_cases hr : r = r1
  · subst hr
    rw [ho] at h1; cases h1
    refine ⟨v, by simp [get_reinsert], ?_⟩
    intro p x hp
    cases p with
    | nil =>
      rw [get_nil] at hp; cases hp
      refine ⟨v, get_nil _, fun T hT => absurd hold (flat_not_ref hT), fun es hes => ?_⟩
      cases old <;> simp_all [IsRef, Val.elems?]
    | cons i q => cases old <;> simp_all [IsRef, Val.get?, Val.children?, Val.elems?]
  · exact ⟨v1, by simp [get_reinsert, hr, h1], Refines.refl _⟩

theorem write_root (s : Store) (r : RootInst) (old v : Val) (ho : s.roots[r]? = some old) :
    s.write ⟨r, []⟩ v = .ok ⟨(s.roots.erase r).insert r v⟩ := by
  simp [Store.write, Store.modify, ho, Val.get?, Val.modifyAt?]

theorem StoreInv.rebind {m : Module} {G : Nat} {s : St} {r : RootInst} {old v : Val}
    (hi : StoreInv m G s) (ho : s.store.roots[r]? = some old) (hold : IsRef old)
    (hv : Held m G s.store v) (hage : ∀ r', Targets v r' → Older r' r) :
    StoreInv m G { s with store := ⟨(s.store.roots.erase r).insert r v⟩ } := by
  have hle := rebind_le s.store r old v ho hold
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r1 v1 h1
    simp only [get_reinsert] at h1
    by_cases hr : r = r1
    · simp only [hr, if_true, Option.some.injEq] at h1
      subst h1; exact hv.mono hle
    · simp only [hr, if_false] at h1
      exact (hi.live r1 v1 h1).mono hle
  · intro r1 v1 h1 r' ht
    simp only [get_reinsert] at h1
    by_cases hr : r = r1
    · simp only [hr, if_true, Option.some.injEq] at h1
      subst h1; subst hr; exact hage r' ht
    · simp only [hr, if_false] at h1
      exact hi.age r1 v1 h1 r' ht
  · intro a si x hx
    simp only [get_reinsert] at hx
    by_cases hr : r = .local a si x
    · subst hr; exact hi.fresh a si x (by simp [ho])
    · simp only [hr, if_false] at hx
      exact hi.fresh a si x hx
  · intro g gl hg hgl
    exact LocTy.mono hle (hi.globals g gl hg hgl)

end Goose.Core.Sound

import Goose.Core.Eval
import Goose.Core.Typing

/-!
Facts about the store: what a typed location is, how a store changes without
invalidating one, and that growth keeps every location valid and every
element it already held.
-/

namespace Goose.Proofs.Memory
open Goose.Core

/-- Typing of a flat value, which holds no reference and needs no store. -/
def FlatTy : Ty → Val → Prop
  | .int t, .int u _ => t = u
  | .bool, .bool _ => True
  | .arr E k, .fixed es => es.size = k ∧ ∀ (i : Nat) (e : Val), es[i]? = some e → FlatTy E e
  | .grow E, .resizable E' es => E = E' ∧ ∀ (i : Nat) (e : Val), es[i]? = some e → FlatTy E e
  | _, _ => False

/-- The location holds a value of flat type `T`. -/
def LocTy (s : Store) (l : Loc) (T : Ty) : Prop :=
  ∃ v, s.read l = .ok v ∧ FlatTy T v

/-- `v'` is `v` after type-preserving writes and growth: every sub-value of
`v` is still there, with every flat type it had and no fewer elements. -/
def Refines (v v' : Val) : Prop :=
  ∀ p x, v.get? p = some x →
    ∃ x', v'.get? p = some x' ∧ (∀ T, FlatTy T x → FlatTy T x') ∧
      ∀ es, x.elems? = some es → ∃ es', x'.elems? = some es' ∧ es.size ≤ es'.size

theorem Refines.refl (v : Val) : Refines v v := by
  intro p x h
  exact ⟨x, h, fun _ h => h, fun es h => ⟨es, h, Nat.le_refl _⟩⟩

theorem Refines.trans {a b c : Val} (h1 : Refines a b) (h2 : Refines b c) : Refines a c := by
  intro p x hx
  obtain ⟨y, hy, ty, sy⟩ := h1 p x hx
  obtain ⟨z, hz, tz, sz⟩ := h2 p y hy
  refine ⟨z, hz, fun T h => tz T (ty T h), fun es hes => ?_⟩
  obtain ⟨es', h', hle⟩ := sy es hes
  obtain ⟨es'', h'', hle'⟩ := sz es' h'
  exact ⟨es'', h'', Nat.le_trans hle hle'⟩

theorem get_nil (v : Val) : v.get? [] = some v := by simp [Val.get?]

theorem get_fixed (es : Array Val) (i : Nat) (rest : List Nat) :
    (Val.fixed es).get? (i :: rest) = (es[i]?).bind (fun e => e.get? rest) := by
  simp [Val.get?, Val.children?, Val.elems?]
  cases es[i]? <;> rfl

theorem get_resizable (E : Ty) (es : Array Val) (i : Nat) (rest : List Nat) :
    (Val.resizable E es).get? (i :: rest) = (es[i]?).bind (fun e => e.get? rest) := by
  simp [Val.get?, Val.children?, Val.elems?]
  cases es[i]? <;> rfl


theorem get_record (sid : StructId) (es : Array Val) (i : Nat) (rest : List Nat) :
    (Val.record sid es).get? (i :: rest) = (es[i]?).bind (fun e => e.get? rest) := by
  simp [Val.get?, Val.children?]
  cases es[i]? <;> rfl


theorem flat_fixed_set (T : Ty) (es : Array Val) (i : Nat) (hi : i < es.size) (e' : Val)
    (h : FlatTy T (.fixed es)) (hT : ∀ T', FlatTy T' es[i] → FlatTy T' e') :
    FlatTy T (.fixed (es.set i e' hi)) := by
  cases T <;> simp only [FlatTy] at h ⊢
  rename_i E k
  refine ⟨by simpa using h.1, fun j e2 hj => ?_⟩
  rw [Array.getElem?_set] at hj
  split at hj
  · rename_i hij
    cases hj
    subst hij
    exact hT E (h.2 i es[i] (by simp [Array.getElem?_eq_getElem hi]))
  · exact h.2 j e2 hj

theorem flat_resizable_set (T E0 : Ty) (es : Array Val) (i : Nat) (hi : i < es.size) (e' : Val)
    (h : FlatTy T (.resizable E0 es)) (hT : ∀ T', FlatTy T' es[i] → FlatTy T' e') :
    FlatTy T (.resizable E0 (es.set i e' hi)) := by
  cases T <;> simp only [FlatTy] at h ⊢
  rename_i E
  refine ⟨h.1, fun j e2 hj => ?_⟩
  rw [Array.getElem?_set] at hj
  split at hj
  · rename_i hij
    cases hj
    subst hij
    exact hT E (h.2 i es[i] (by simp [Array.getElem?_eq_getElem hi]))
  · exact h.2 j e2 hj


/-- Replacing the sub-value at a path by one that refines it refines the whole. -/
theorem refines_modifyAt (f : Val → Option Val) :
    ∀ (p : List Nat) (v v' x y : Val), v.modifyAt? p f = some v' → v.get? p = some x →
      f x = some y → Refines x y → Refines v v' := by
  intro p
  induction p with
  | nil =>
    intro v v' x y h1 h2 h3 h4
    simp [Val.modifyAt?] at h1
    simp [Val.get?] at h2
    subst h2
    rw [h3] at h1
    cases h1
    exact h4
  | cons i rest ih =>
    intro v v' x y h1 h2 h3 h4
    cases v with
    | fixed es =>
      simp only [Val.modifyAt?] at h1
      split at h1
      · rename_i hi
        split at h1
        · rename_i e' he'
          cases h1
          rw [get_fixed, Array.getElem?_eq_getElem hi] at h2
          simp only [Option.bind_some] at h2
          have hr := ih es[i] e' x y he' h2 h3 h4
          have hr0 := hr [] es[i] (get_nil _)
          obtain ⟨x0, hx0, hT0, hs0⟩ := hr0
          rw [get_nil] at hx0; cases hx0
          intro q w hq
          cases q with
          | nil =>
            rw [get_nil] at hq; cases hq
            refine ⟨_, get_nil _, fun T hT => flat_fixed_set T es i hi _ hT hT0, fun es' hes' => ?_⟩
            simp only [Val.elems?, Option.some.injEq] at hes'
            subst hes'
            exact ⟨_, rfl, by simp⟩
          | cons j q' =>
            rw [get_fixed] at hq
            rw [get_fixed]
            by_cases hij : i = j
            · subst hij
              rw [Array.getElem?_eq_getElem hi] at hq
              simp only [Option.bind_some] at hq
              rw [Array.getElem?_set_self hi]
              simp only [Option.bind_some]
              exact hr q' w hq
            · rw [Array.getElem?_set]; simp only [hij, ite_false]
              exact ⟨w, hq, fun _ h => h, fun es h => ⟨es, h, Nat.le_refl _⟩⟩
        · simp at h1
      · simp at h1
    | record sid es =>
      simp only [Val.modifyAt?] at h1
      split at h1
      · rename_i hi
        split at h1
        · rename_i e' he'
          cases h1
          rw [get_record, Array.getElem?_eq_getElem hi] at h2
          simp only [Option.bind_some] at h2
          have hr := ih es[i] e' x y he' h2 h3 h4
          have hr0 := hr [] es[i] (get_nil _)
          obtain ⟨x0, hx0, hT0, hs0⟩ := hr0
          rw [get_nil] at hx0; cases hx0
          intro q w hq
          cases q with
          | nil =>
            rw [get_nil] at hq; cases hq
            refine ⟨_, get_nil _, ?_, ?_⟩
            · intro T hT; cases T <;> simp [FlatTy] at hT
            · intro es' hes'; simp [Val.elems?] at hes'
          | cons j q' =>
            rw [get_record] at hq
            rw [get_record]
            by_cases hij : i = j
            · subst hij
              rw [Array.getElem?_eq_getElem hi] at hq
              simp only [Option.bind_some] at hq
              rw [Array.getElem?_set_self hi]
              simp only [Option.bind_some]
              exact hr q' w hq
            · rw [Array.getElem?_set]; simp only [hij, ite_false]
              exact ⟨w, hq, fun _ h => h, fun es h => ⟨es, h, Nat.le_refl _⟩⟩
        · simp at h1
      · simp at h1
    | resizable E0 es =>
      simp only [Val.modifyAt?] at h1
      split at h1
      · rename_i hi
        split at h1
        · rename_i e' he'
          cases h1
          rw [get_resizable, Array.getElem?_eq_getElem hi] at h2
          simp only [Option.bind_some] at h2
          have hr := ih es[i] e' x y he' h2 h3 h4
          have hr0 := hr [] es[i] (get_nil _)
          obtain ⟨x0, hx0, hT0, hs0⟩ := hr0
          rw [get_nil] at hx0; cases hx0
          intro q w hq
          cases q with
          | nil =>
            rw [get_nil] at hq; cases hq
            refine ⟨_, get_nil _, fun T hT => flat_resizable_set T E0 es i hi _ hT hT0, fun es' hes' => ?_⟩
            simp only [Val.elems?, Option.some.injEq] at hes'
            subst hes'
            exact ⟨_, rfl, by simp⟩
          | cons j q' =>
            rw [get_resizable] at hq
            rw [get_resizable]
            by_cases hij : i = j
            · subst hij
              rw [Array.getElem?_eq_getElem hi] at hq
              simp only [Option.bind_some] at hq
              rw [Array.getElem?_set_self hi]
              simp only [Option.bind_some]
              exact hr q' w hq
            · rw [Array.getElem?_set]; simp only [hij, ite_false]
              exact ⟨w, hq, fun _ h => h, fun es h => ⟨es, h, Nat.le_refl _⟩⟩
        · simp at h1
      · simp at h1
    | _ => simp [Val.modifyAt?] at h1


/-! ### The store -/

def StoreLe (s s' : Store) : Prop :=
  ∀ (r : RootInst) (v : Val), s.roots[r]? = some v → ∃ v', s'.roots[r]? = some v' ∧ Refines v v'

theorem StoreLe.refl (s : Store) : StoreLe s s :=
  fun _ v h => ⟨v, h, Refines.refl v⟩

theorem StoreLe.trans {a b c : Store} (h1 : StoreLe a b) (h2 : StoreLe b c) : StoreLe a c := by
  intro r v hv
  obtain ⟨v1, hv1, r1⟩ := h1 r v hv
  obtain ⟨v2, hv2, r2⟩ := h2 r v1 hv1
  exact ⟨v2, hv2, r1.trans r2⟩

theorem read_ok_iff (s : Store) (l : Loc) (v : Val) :
    s.read l = .ok v ↔ ∃ old, s.roots[l.root]? = some old ∧ old.get? l.path = some v := by
  unfold Store.read
  cases h : s.roots[l.root]? with
  | none => simp
  | some old =>
    cases h2 : old.get? l.path with
    | none => simp [h2]
    | some x => simp [h2, eq_comm]

theorem LocTy.mono {s s' : Store} {l : Loc} {T : Ty} (hle : StoreLe s s') (h : LocTy s l T) :
    LocTy s' l T := by
  obtain ⟨v, hv, hT⟩ := h
  obtain ⟨old, ho, hg⟩ := (read_ok_iff _ _ _).1 hv
  obtain ⟨old', ho', hr⟩ := hle _ _ ho
  obtain ⟨x', hx', hT', _⟩ := hr _ _ hg
  exact ⟨x', (read_ok_iff _ _ _).2 ⟨old', ho', hx'⟩, hT' T hT⟩

theorem modifyAt_spec (f : Val → Option Val) :
    ∀ (p : List Nat) (v v' x : Val), v.modifyAt? p f = some v' → v.get? p = some x →
      ∃ y, f x = some y := by
  intro p
  induction p with
  | nil =>
    intro v v' x h1 h2
    simp [Val.modifyAt?] at h1
    simp [Val.get?] at h2
    subst h2
    exact ⟨v', h1⟩
  | cons i rest ih =>
    intro v v' x h1 h2
    cases v with
    | fixed es =>
      simp only [Val.modifyAt?] at h1
      split at h1
      · rename_i hi
        split at h1
        · rename_i e' he'
          rw [get_fixed, Array.getElem?_eq_getElem hi] at h2
          simp only [Option.bind_some] at h2
          exact ih es[i] e' x he' h2
        · simp at h1
      · simp at h1
    | record sid es =>
      simp only [Val.modifyAt?] at h1
      split at h1
      · rename_i hi
        split at h1
        · rename_i e' he'
          rw [get_record, Array.getElem?_eq_getElem hi] at h2
          simp only [Option.bind_some] at h2
          exact ih es[i] e' x he' h2
        · simp at h1
      · simp at h1
    | resizable E0 es =>
      simp only [Val.modifyAt?] at h1
      split at h1
      · rename_i hi
        split at h1
        · rename_i e' he'
          rw [get_resizable, Array.getElem?_eq_getElem hi] at h2
          simp only [Option.bind_some] at h2
          exact ih es[i] e' x he' h2
        · simp at h1
      · simp at h1
    | _ => simp [Val.modifyAt?] at h1

theorem modify_spec (s s' : Store) (l : Loc) (f : Val → Option Val)
    (h : s.modify l f = .ok s') :
    ∃ old x y new, s.roots[l.root]? = some old ∧ old.get? l.path = some x ∧ f x = some y ∧
      old.modifyAt? l.path f = some new ∧
      s'.roots = (s.roots.erase l.root).insert l.root new := by
  unfold Store.modify at h
  cases h1 : s.roots[l.root]? with
  | none => simp [h1] at h
  | some old =>
    simp only [h1] at h
    cases h2 : old.get? l.path with
    | none => simp [h2] at h
    | some x =>
      simp only [h2] at h
      cases h3 : old.modifyAt? l.path f with
      | none => simp [h3] at h
      | some new =>
        simp only [h3, Except.ok.injEq] at h
        obtain ⟨y, hy⟩ := modifyAt_spec f l.path old new x h3 h2
        refine ⟨old, x, y, new, rfl, h2, hy, h3, ?_⟩
        rw [← h]

/-- A rewrite of one location that refines the old sub-value refines the store. -/
theorem modify_le (s s' : Store) (l : Loc) (f : Val → Option Val)
    (h : s.modify l f = .ok s')
    (hf : ∀ old x y, s.roots[l.root]? = some old → old.get? l.path = some x →
      f x = some y → Refines x y) : StoreLe s s' := by
  obtain ⟨old, x, y, new, h1, h2, h3, h4, h5⟩ := modify_spec s s' l f h
  intro r v hv
  by_cases hr : r = l.root
  · subst hr
    rw [h1] at hv; cases hv
    refine ⟨new, ?_, refines_modifyAt f l.path old new x y h4 h2 h3 (hf old x y h1 h2 h3)⟩
    rw [h5]; simp
  · refine ⟨v, ?_, Refines.refl v⟩
    rw [h5]
    have : l.root ≠ r := fun e => hr e.symm
    simp [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, this, hv]


/-- A flat type is determined by any value of it, so a value of the same
flat type has every type the old value had. -/
theorem flat_swap : ∀ (T : Ty), T.flat = true → ∀ (x y : Val) (T' : Ty),
    FlatTy T x → FlatTy T y → FlatTy T' x → FlatTy T' y
  | .int t, _, x, y, T', hx, hy, hx' => by
    cases x <;> cases y <;> simp only [FlatTy] at hx hy
    cases T' <;> simp only [FlatTy] at hx' ⊢
    subst hx; subst hy; exact hx'
  | .bool, _, x, y, T', hx, hy, hx' => by
    cases x <;> cases y <;> simp only [FlatTy] at hx hy
    cases T' <;> simp only [FlatTy] at hx' ⊢
  | .arr E k, hf, x, y, T', hx, hy, hx' => by
    cases x <;> cases y <;> simp only [FlatTy] at hx hy
    rename_i es vs
    cases T' <;> simp only [FlatTy] at hx' ⊢
    rename_i E' k'
    have hvs : vs.size = k' := by omega
    refine ⟨hvs, fun i e he => ?_⟩
    obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.1 he
    have hi2 : i < es.size := by omega
    have hfE : E.flat = true := by simpa [Ty.flat] using hf
    exact flat_swap E hfE es[i] e E' (hx.2 i _ (Array.getElem?_eq_getElem hi2))
      (hy.2 i e he) (hx'.2 i _ (Array.getElem?_eq_getElem hi2))
  | .structT _ _, _, x, _, _, hx, _, _ => by cases x <;> simp [FlatTy] at hx
  | .unit, hf, _, _, _, _, _, _ => by simp [Ty.flat] at hf
  | .grow _, hf, _, _, _, _, _, _ => by simp [Ty.flat] at hf
  | .ref _ _, hf, _, _, _, _, _, _ => by simp [Ty.flat] at hf
  | .slice _ _, hf, _, _, _, _, _, _ => by simp [Ty.flat] at hf
  | .tuple _, hf, _, _, _, _, _, _ => by simp [Ty.flat] at hf


/-- Overwriting a flat value with another of the same flat type refines it. -/
theorem flat_refines : ∀ (T : Ty), T.flat = true → ∀ (x y : Val),
    FlatTy T x → FlatTy T y → Refines x y
  | .int t, hf, x, y, hx, hy => by
    intro p x0 hp
    cases p with
    | cons i q => rcases x with _|_|_|_|_|_|_|_ <;> simp [FlatTy, Val.get?, Val.children?, Val.elems?] at hx hp
    | nil =>
      rw [get_nil] at hp; cases hp
      refine ⟨y, get_nil _, fun T' h => flat_swap _ hf _ y T' hx hy h, fun es hes => ?_⟩
      rcases x with _|_|_|_|_|_|_|_ <;> simp [FlatTy, Val.elems?] at hx hes
  | .bool, hf, x, y, hx, hy => by
    intro p x0 hp
    cases p with
    | cons i q => rcases x with _|_|_|_|_|_|_|_ <;> simp [FlatTy, Val.get?, Val.children?, Val.elems?] at hx hp
    | nil =>
      rw [get_nil] at hp; cases hp
      refine ⟨y, get_nil _, fun T' h => flat_swap _ hf _ y T' hx hy h, fun es hes => ?_⟩
      rcases x with _|_|_|_|_|_|_|_ <;> simp [FlatTy, Val.elems?] at hx hes
  | .arr E k, hf, x, y, hx, hy => by
    have hfE : E.flat = true := by simpa [Ty.flat] using hf
    cases x <;> cases y <;> simp only [FlatTy] at hx hy
    rename_i es vs
    intro p x0 hp
    cases p with
    | nil =>
      rw [get_nil] at hp; cases hp
      refine ⟨_, get_nil _, fun T' h => flat_swap _ hf _ _ T' (by simpa [FlatTy] using hx) (by simpa [FlatTy] using hy) h, fun es' hes' => ?_⟩
      simp only [Val.elems?, Option.some.injEq] at hes'
      subst hes'
      exact ⟨vs, rfl, by omega⟩
    | cons i q =>
      rw [get_fixed] at hp
      cases hei : es[i]? with
      | none => simp [hei] at hp
      | some e =>
        simp only [hei, Option.bind_some] at hp
        obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.1 hei
        have hi2 : i < vs.size := by omega
        have hr := flat_refines E hfE e vs[i] (hx.2 i e hei) (hy.2 i _ (Array.getElem?_eq_getElem hi2)) q x0 hp
        obtain ⟨x', hx', ht, hs⟩ := hr
        refine ⟨x', ?_, ht, hs⟩
        rw [get_fixed, Array.getElem?_eq_getElem hi2]
        simpa using hx'
  | .structT _ _, _, x, _, hx, _ => by cases x <;> simp [FlatTy] at hx
  | .unit, hf, _, _, _, _ => by simp [Ty.flat] at hf
  | .grow _, hf, _, _, _, _ => by simp [Ty.flat] at hf
  | .ref _ _, hf, _, _, _, _ => by simp [Ty.flat] at hf
  | .slice _ _, hf, _, _, _, _ => by simp [Ty.flat] at hf
  | .tuple _, hf, _, _, _, _ => by simp [Ty.flat] at hf

/-- A write of a value of the location's flat type keeps every typed location typed. -/
theorem write_le (s s' : Store) (l : Loc) (v : Val) (T : Ty) (hT : T.flat = true)
    (hl : LocTy s l T) (hv : FlatTy T v) (h : s.write l v = .ok s') :
    StoreLe s s' ∧ LocTy s' l T := by
  have hle : StoreLe s s' := by
    apply modify_le s s' l _ h
    intro old x y ho hx hxy
    obtain ⟨x1, hx1, hT1⟩ := hl
    obtain ⟨old1, ho1, hg1⟩ := (read_ok_iff _ _ _).1 hx1
    rw [ho] at ho1; cases ho1
    rw [hx] at hg1; cases hg1
    simp only [Option.some.injEq] at hxy
    subst hxy
    exact flat_refines T hT _ _ hT1 hv
  exact ⟨hle, LocTy.mono hle hl⟩


theorem refines_push (E : Ty) (es vs : Array Val) (hvs : ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e) :
    Refines (.resizable E es) (.resizable E (es ++ vs)) := by
  intro p x hp
  cases p with
  | nil =>
    rw [get_nil] at hp; cases hp
    refine ⟨_, get_nil _, fun T' hT' => ?_, fun es' hes' => ?_⟩
    · cases T' <;> simp only [FlatTy] at hT' ⊢
      refine ⟨hT'.1, fun i e he => ?_⟩
      by_cases hi : i < es.size
      · rw [Array.getElem?_append_left hi] at he
        exact hT'.2 i e he
      · rw [Array.getElem?_append_right (by omega)] at he
        have := hvs _ e he
        rw [hT'.1]; exact this
    · simp only [Val.elems?, Option.some.injEq] at hes'
      subst hes'
      exact ⟨es ++ vs, rfl, by simp⟩
  | cons i q =>
    rw [get_resizable] at hp
    cases hei : es[i]? with
    | none => simp [hei] at hp
    | some e =>
      simp only [hei, Option.bind_some] at hp
      obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.1 hei
      refine ⟨x, ?_, fun _ h => h, fun es h => ⟨es, h, Nat.le_refl _⟩⟩
      rw [get_resizable, Array.getElem?_append_left hi, hei]
      simpa using hp

theorem get_append (v : Val) : ∀ (p q : List Nat), v.get? (p ++ q) = (v.get? p).bind (fun x => x.get? q) := by
  intro p
  induction p generalizing v with
  | nil => intro q; simp [get_nil]
  | cons i rest ih =>
    intro q
    rcases v with _|_|_|es|⟨sid, fields⟩|⟨E, es⟩|_|_
    all_goals simp [Val.get?, Val.children?, Val.elems?]
    · cases es[i]? <;> simp [ih]
    · cases fields[i]? <;> simp [ih]
    · cases es[i]? <;> simp [ih]

theorem modifyAt_get_same (f : Val → Option Val) :
    ∀ (p : List Nat) (v v' x y : Val), v.modifyAt? p f = some v' → v.get? p = some x →
      f x = some y → v'.get? p = some y := by
  intro p
  induction p with
  | nil =>
    intro v v' x y h1 h2 h3
    simp [Val.modifyAt?] at h1
    simp [Val.get?] at h2
    subst h2
    rw [h3] at h1; cases h1
    simp [Val.get?]
  | cons i rest ih =>
    intro v v' x y h1 h2 h3
    cases v with
    | fixed es =>
      simp only [Val.modifyAt?] at h1
      split at h1
      · rename_i hi
        split at h1
        · rename_i e' he'
          cases h1
          rw [get_fixed, Array.getElem?_eq_getElem hi] at h2
          simp only [Option.bind_some] at h2
          rw [get_fixed, Array.getElem?_set_self hi]
          simpa using ih es[i] e' x y he' h2 h3
        · simp at h1
      · simp at h1
    | record sid es =>
      simp only [Val.modifyAt?] at h1
      split at h1
      · rename_i hi
        split at h1
        · rename_i e' he'
          cases h1
          rw [get_record, Array.getElem?_eq_getElem hi] at h2
          simp only [Option.bind_some] at h2
          rw [get_record, Array.getElem?_set_self hi]
          simpa using ih es[i] e' x y he' h2 h3
        · simp at h1
      · simp at h1
    | resizable E0 es =>
      simp only [Val.modifyAt?] at h1
      split at h1
      · rename_i hi
        split at h1
        · rename_i e' he'
          cases h1
          rw [get_resizable, Array.getElem?_eq_getElem hi] at h2
          simp only [Option.bind_some] at h2
          rw [get_resizable, Array.getElem?_set_self hi]
          simpa using ih es[i] e' x y he' h2 h3
        · simp at h1
      · simp at h1
    | _ => simp [Val.modifyAt?] at h1


theorem length_ok (s : Store) (l : Loc) (n : Nat) (h : s.length l = .ok n) :
    ∃ E es, s.read l = .ok (.resizable E es) ∧ n = es.size := by
  unfold Store.length at h
  cases hr : s.read l with
  | error k => simp [hr] at h
  | ok v =>
    rcases v with _|_|_|_|_|⟨E, es⟩|_|_ <;> simp [hr] at h
    exact ⟨E, es, rfl, h.symm⟩

theorem append_spec (s s' : Store) (l : Loc) (vs : Array Val) (n : Nat)
    (h : s.append l vs = .ok (s', n)) :
    ∃ E es, s.read l = .ok (.resizable E es) ∧ n = es.size ∧
      s.modify l (Val.appendAll vs) = .ok s' := by
  unfold Store.append at h
  cases hl : s.length l with
  | error k => simp [hl] at h
  | ok n0 =>
    simp only [hl] at h
    cases hm : s.modify l (Val.appendAll vs) with
    | error k => simp [hm] at h
    | ok s1 =>
      simp only [hm, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨E, es, hr, hn⟩ := length_ok s l n0 hl
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2
      exact ⟨E, es, hr, hn, rfl⟩

/-- `TH-MEM-01` store-level core: growth keeps every typed location typed, keeps
every sub-value that existed, and the new elements are read where expected. -/
theorem append_le (s s' : Store) (l : Loc) (vs : Array Val) (n : Nat) (E : Ty)
    (hl : LocTy s l (.grow E)) (hvs : ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e)
    (h : s.append l vs = .ok (s', n)) :
    StoreLe s s' ∧ LocTy s' l (.grow E) ∧
      ∃ es, s.read l = .ok (.resizable E es) ∧ n = es.size ∧
        ∀ (i : Nat) (e : Val), vs[i]? = some e →
          s'.read ⟨l.root, l.path ++ [n + i]⟩ = .ok e := by
  obtain ⟨E1, es, hr, hn, hm⟩ := append_spec s s' l vs n h
  have hE : E = E1 := by
    obtain ⟨x, hx, hT⟩ := hl
    rw [hr] at hx; cases hx
    simpa [FlatTy] using hT.1
  subst hE
  have hle : StoreLe s s' := by
    apply modify_le s s' l _ hm
    intro old x0 y ho hx0 hxy
    obtain ⟨old1, ho1, hg1⟩ := (read_ok_iff _ _ _).1 hr
    rw [ho] at ho1; cases ho1
    rw [hx0] at hg1; cases hg1
    simp only [Val.appendAll, Option.some.injEq] at hxy
    subst hxy
    exact refines_push E es vs hvs
  have hnew : LocTy s' l (.grow E) := LocTy.mono hle hl
  refine ⟨hle, hnew, es, hr, hn, ?_⟩
  intro i e he
  obtain ⟨old, x, y, new, ho, hx, hy, hmod, hroots⟩ := modify_spec s s' l _ hm
  obtain ⟨old1, ho1, hg1⟩ := (read_ok_iff _ _ _).1 hr
  rw [ho] at ho1; cases ho1
  rw [hx] at hg1; cases hg1
  simp only [Val.appendAll, Option.some.injEq] at hy
  have hg := modifyAt_get_same (Val.appendAll vs) l.path old new (.resizable E es) (.resizable E (es ++ vs)) hmod hx (by simp [Val.appendAll])
  rw [read_ok_iff]
  refine ⟨new, ?_, ?_⟩
  · rw [hroots]; simp
  · rw [get_append, hg]
    simp only [Option.bind_some]
    rw [get_resizable, Array.getElem?_append_right (by omega)]
    have : n + i - es.size = i := by omega
    rw [this, he]
    simp [get_nil]


/-- Rewriting the sub-value at `p` keeps every sub-location that existed, and
leaves untouched every one that is not on the way down to `p`, provided the new
sub-value keeps every proper sub-location of the old one. -/
theorem modifyAt_preserve (f : Val → Option Val) :
    ∀ (p : List Nat) (v v' x y : Val), v.modifyAt? p f = some v' → v.get? p = some x →
      f x = some y → (∀ r z, r ≠ [] → x.get? r = some z → y.get? r = some z) →
      ∀ q z, v.get? q = some z →
        (¬ q <+: p → v'.get? q = some z) ∧ (q <+: p → ∃ z', v'.get? q = some z') := by
  intro p
  induction p with
  | nil =>
    intro v v' x y h1 h2 h3 h4 q z hq
    simp [Val.modifyAt?] at h1
    simp [Val.get?] at h2
    subst h2
    rw [h3] at h1; cases h1
    refine ⟨fun hn => ?_, fun hp => ?_⟩
    · have : q ≠ [] := fun e => hn (by simp [e])
      exact h4 q z this hq
    · have hq0 : q = [] := List.prefix_nil.1 hp
      subst hq0
      exact ⟨_, get_nil _⟩
  | cons i rest ih =>
    intro v v' x y h1 h2 h3 h4 q z hq
    cases v with
    | fixed es =>
      simp only [Val.modifyAt?] at h1
      split at h1
      · rename_i hi
        split at h1
        · rename_i e' he'
          cases h1
          rw [get_fixed, Array.getElem?_eq_getElem hi] at h2
          simp only [Option.bind_some] at h2
          cases q with
          | nil =>
            refine ⟨fun hn => absurd (List.nil_prefix) hn, fun _ => ⟨_, get_nil _⟩⟩
          | cons j q' =>
            rw [get_fixed] at hq
            rw [get_fixed]
            by_cases hij : i = j
            · subst hij
              rw [Array.getElem?_eq_getElem hi] at hq
              simp only [Option.bind_some] at hq
              rw [Array.getElem?_set_self hi]
              simp only [Option.bind_some]
              have := ih es[i] e' x y he' h2 h3 h4 q' z hq
              refine ⟨fun hn => this.1 (fun hp => hn (by simpa using hp)), fun hp => this.2 (by simpa using hp)⟩
            · rw [Array.getElem?_set]; simp only [hij, ite_false]
              exact ⟨fun _ => hq, fun hp => absurd (List.cons_prefix_cons.1 hp).1.symm hij⟩
        · simp at h1
      · simp at h1
    | record sid es =>
      simp only [Val.modifyAt?] at h1
      split at h1
      · rename_i hi
        split at h1
        · rename_i e' he'
          cases h1
          rw [get_record, Array.getElem?_eq_getElem hi] at h2
          simp only [Option.bind_some] at h2
          cases q with
          | nil =>
            refine ⟨fun hn => absurd (List.nil_prefix) hn, fun _ => ⟨_, get_nil _⟩⟩
          | cons j q' =>
            rw [get_record] at hq
            rw [get_record]
            by_cases hij : i = j
            · subst hij
              rw [Array.getElem?_eq_getElem hi] at hq
              simp only [Option.bind_some] at hq
              rw [Array.getElem?_set_self hi]
              simp only [Option.bind_some]
              have := ih es[i] e' x y he' h2 h3 h4 q' z hq
              refine ⟨fun hn => this.1 (fun hp => hn (by simpa using hp)), fun hp => this.2 (by simpa using hp)⟩
            · rw [Array.getElem?_set]; simp only [hij, ite_false]
              exact ⟨fun _ => hq, fun hp => absurd (List.cons_prefix_cons.1 hp).1.symm hij⟩
        · simp at h1
      · simp at h1
    | resizable E0 es =>
      simp only [Val.modifyAt?] at h1
      split at h1
      · rename_i hi
        split at h1
        · rename_i e' he'
          cases h1
          rw [get_resizable, Array.getElem?_eq_getElem hi] at h2
          simp only [Option.bind_some] at h2
          cases q with
          | nil =>
            refine ⟨fun hn => absurd (List.nil_prefix) hn, fun _ => ⟨_, get_nil _⟩⟩
          | cons j q' =>
            rw [get_resizable] at hq
            rw [get_resizable]
            by_cases hij : i = j
            · subst hij
              rw [Array.getElem?_eq_getElem hi] at hq
              simp only [Option.bind_some] at hq
              rw [Array.getElem?_set_self hi]
              simp only [Option.bind_some]
              have := ih es[i] e' x y he' h2 h3 h4 q' z hq
              refine ⟨fun hn => this.1 (fun hp => hn (by simpa using hp)), fun hp => this.2 (by simpa using hp)⟩
            · rw [Array.getElem?_set]; simp only [hij, ite_false]
              exact ⟨fun _ => hq, fun hp => absurd (List.cons_prefix_cons.1 hp).1.symm hij⟩
        · simp at h1
      · simp at h1
    | _ => simp [Val.modifyAt?] at h1


theorem appendAll_keeps (E : Ty) (es vs : Array Val) :
    ∀ (r : List Nat) (z : Val), r ≠ [] → (Val.resizable E es).get? r = some z →
      (Val.resizable E (es ++ vs)).get? r = some z := by
  intro r z hr hz
  cases r with
  | nil => exact absurd rfl hr
  | cons i q =>
    rw [get_resizable] at hz ⊢
    cases hei : es[i]? with
    | none => simp [hei] at hz
    | some e =>
      simp only [hei, Option.bind_some] at hz
      obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.1 hei
      rw [Array.getElem?_append_left hi, hei]
      simpa using hz

/-- `TH-MEM-01`: growth keeps every valid location valid and, unless the
location is the grown array or one that contains it, keeps its content. -/
theorem th_mem_01 (s s' : Store) (o : Loc) (vs : Array Val) (n : Nat)
    (h : s.append o vs = .ok (s', n)) :
    (∀ (l : Loc) (v : Val), s.read l = .ok v → ∃ v', s'.read l = .ok v') ∧
    (∀ (l : Loc) (v : Val), s.read l = .ok v →
        ¬ (l.root = o.root ∧ l.path <+: o.path) → s'.read l = .ok v) := by
  obtain ⟨E, es, hr, hn, hm⟩ := append_spec s s' o vs n h
  obtain ⟨old, x, y, new, ho, hx, hy, hmod, hroots⟩ := modify_spec s s' o _ hm
  obtain ⟨old1, ho1, hg1⟩ := (read_ok_iff _ _ _).1 hr
  rw [ho] at ho1; cases ho1
  rw [hx] at hg1; cases hg1
  simp only [Val.appendAll, Option.some.injEq] at hy
  subst hy
  have hkeep := modifyAt_preserve (Val.appendAll vs) o.path old new _ _ hmod hx
    (by simp [Val.appendAll]) (appendAll_keeps E es vs)
  have other : ∀ (l : Loc), l.root ≠ o.root → s'.roots[l.root]? = s.roots[l.root]? := by
    intro l hl
    rw [hroots]
    simp [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Ne.symm hl]
  constructor
  · intro l v hv
    obtain ⟨ol, hol, hgl⟩ := (read_ok_iff _ _ _).1 hv
    by_cases hlr : l.root = o.root
    · rw [hlr] at hol
      rw [ho] at hol; cases hol
      by_cases hp : l.path <+: o.path
      · obtain ⟨z', hz'⟩ := (hkeep l.path v hgl).2 hp
        exact ⟨z', (read_ok_iff _ _ _).2 ⟨new, by rw [hlr, hroots]; simp, hz'⟩⟩
      · exact ⟨v, (read_ok_iff _ _ _).2 ⟨new, by rw [hlr, hroots]; simp, (hkeep l.path v hgl).1 hp⟩⟩
    · exact ⟨v, (read_ok_iff _ _ _).2 ⟨ol, by rw [other l hlr]; exact hol, hgl⟩⟩
  · intro l v hv hn'
    obtain ⟨ol, hol, hgl⟩ := (read_ok_iff _ _ _).1 hv
    by_cases hlr : l.root = o.root
    · rw [hlr] at hol
      rw [ho] at hol; cases hol
      have hp : ¬ l.path <+: o.path := fun hp => hn' ⟨hlr, hp⟩
      exact (read_ok_iff _ _ _).2 ⟨new, by rw [hlr, hroots]; simp, (hkeep l.path v hgl).1 hp⟩
    · exact (read_ok_iff _ _ _).2 ⟨ol, by rw [other l hlr]; exact hol, hgl⟩


/-! ### The live-reference invariant

A reference or slice is held only as the whole value of a variable. The
invariant says each one denotes a valid location of an array or flat type. It
is preserved by every memory operation of the evaluator: a type-preserving
write, growth, binding a fresh root, and releasing a scope's roots when no
surviving reference targets one of them. -/

/-- A slice denotes a run inside a valid array location. -/
def SliceOk (s : Store) (l : Loc) (st n : Nat) : Prop :=
  ∃ E, (∃ k, LocTy s l (.arr E k) ∧ st + n ≤ k) ∨
    (LocTy s l (.grow E) ∧ ∃ E' es, s.read l = .ok (.resizable E' es) ∧ st + n ≤ es.size)

/-- A held value is a reference to a valid typed location, a slice of a valid
run, or holds no reference. -/
def HeldOk (s : Store) : Val → Prop
  | .ref l => ∃ T, T.refTarget = true ∧ LocTy s l T
  | .slice l st n => SliceOk s l st n
  | _ => True

def LiveRefs (s : Store) : Prop :=
  ∀ (r : RootInst) (v : Val), s.roots[r]? = some v → HeldOk s v

theorem SliceOk.mono {s s' : Store} {l : Loc} {st n : Nat} (hle : StoreLe s s')
    (h : SliceOk s l st n) : SliceOk s' l st n := by
  obtain ⟨E, h⟩ := h
  refine ⟨E, ?_⟩
  rcases h with ⟨k, hl, hk⟩ | ⟨hl, E', es, hr, hk⟩
  · exact Or.inl ⟨k, LocTy.mono hle hl, hk⟩
  · right
    refine ⟨LocTy.mono hle hl, ?_⟩
    obtain ⟨old, ho, hg⟩ := (read_ok_iff _ _ _).1 hr
    obtain ⟨old', ho', hr'⟩ := hle _ _ ho
    obtain ⟨x', hx', hT, hs⟩ := hr' _ _ hg
    have hflat : FlatTy (.grow E) (.resizable E' es) := by
      obtain ⟨v, hv, hT0⟩ := hl
      rw [hr] at hv; cases hv; exact hT0
    have hx2 := hT _ hflat
    rcases x' with _|_|_|_|_|⟨E2, es2⟩|_|_ <;> simp only [FlatTy] at hx2
    obtain ⟨es', hes', hle'⟩ := hs es (by simp [Val.elems?])
    simp only [Val.elems?, Option.some.injEq] at hes'
    exact ⟨E2, es2, (read_ok_iff _ _ _).2 ⟨old', ho', hx'⟩, by rw [hes']; omega⟩

theorem HeldOk.mono {s s' : Store} {v : Val} (hle : StoreLe s s') (h : HeldOk s v) :
    HeldOk s' v := by
  cases v <;> simp only [HeldOk] at h ⊢
  · obtain ⟨T, hT, hl⟩ := h
    exact ⟨T, hT, LocTy.mono hle hl⟩
  · exact SliceOk.mono hle h

theorem held_of_elems (s : Store) (v : Val) (h : v.elems?.isSome = true) : HeldOk s v := by
  cases v <;> simp_all [HeldOk, Val.elems?]

/-- Binding a root that does not exist yet. -/
theorem introduce_le (s : Store) (r : RootInst) (v : Val) (h : s.roots[r]? = none) :
    StoreLe s (s.introduce r v) := by
  intro r' v' hv'
  refine ⟨v', ?_, Refines.refl v'⟩
  have : r ≠ r' := fun e => by subst e; rw [h] at hv'; cases hv'
  simp [Store.introduce, Std.HashMap.getElem?_insert, this, hv']

theorem liveRefs_introduce (s : Store) (r : RootInst) (v : Val) (h : s.roots[r]? = none)
    (hlr : LiveRefs s) (hv : HeldOk s v) : LiveRefs (s.introduce r v) := by
  have hle := introduce_le s r v h
  intro r' v' hv'
  by_cases hr : r = r'
  · subst hr
    simp [Store.introduce] at hv'
    subst hv'
    exact HeldOk.mono hle hv
  · have : s.roots[r']? = some v' := by
      simpa [Store.introduce, Std.HashMap.getElem?_insert, hr] using hv'
    exact HeldOk.mono hle (hlr r' v' this)

/-- Updating a descendant retains a container root, which holds no direct reference. -/
theorem modifyAt_cons_held (s : Store) (v v' : Val) (i : Nat) (q : List Nat)
    (f : Val → Option Val) (h : v.modifyAt? (i :: q) f = some v') : HeldOk s v' := by
  cases v <;> simp only [Val.modifyAt?] at h
  all_goals first
    | contradiction
    | (split at h
       · split at h
         · cases h; trivial
         · simp at h
       · simp at h)

#guard ((Val.record 0 #[Val.int .i64 1]).get? [0]).isSome = true
#guard (Val.record 0 #[Val.int .i64 1]).elems?.isSome = false

theorem get_cons_children (v z : Val) (i : Nat) (q : List Nat) (h : v.get? (i :: q) = some z) :
    v.children?.isSome = true := by
  rcases v with _|_|_|es|⟨sid, fields⟩|⟨E, es⟩|_|_ <;> simp_all [Val.get?, Val.children?, Val.elems?]

/-- Growth keeps the live-reference invariant. -/
theorem liveRefs_append (s s' : Store) (l : Loc) (vs : Array Val) (n : Nat) (E : Ty)
    (hl : LocTy s l (.grow E)) (hvs : ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e)
    (h : s.append l vs = .ok (s', n)) (hlr : LiveRefs s) : LiveRefs s' := by
  obtain ⟨hle, _, _⟩ := append_le s s' l vs n E hl hvs h
  obtain ⟨E1, es, hr, hn, hm⟩ := append_spec s s' l vs n h
  have hE : E = E1 := by
    obtain ⟨x, hx, hT⟩ := hl
    rw [hr] at hx; cases hx
    simpa [FlatTy] using hT.1
  subst hE
  obtain ⟨old, x, y, new, ho, hx, hy, hmod, hroots⟩ := modify_spec s s' l _ hm
  intro r v hv
  by_cases hrr : r = l.root
  · subst hrr
    rw [hroots] at hv
    simp at hv
    subst hv
    cases hp : l.path with
    | nil =>
      rw [hp, Val.modifyAt?] at hmod
      rw [hp, get_nil] at hx; cases hx
      rw [hy] at hmod; cases hmod
      cases old <;> simp [Val.appendAll] at hy
      cases hy
      trivial
    | cons i q =>
      rw [hp] at hmod
      exact modifyAt_cons_held _ _ _ _ _ _ hmod
  · have : s.roots[r]? = some v := by
      rw [hroots] at hv
      simpa [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Ne.symm hrr] using hv
    exact HeldOk.mono hle (hlr r v this)


theorem flat_held (s : Store) (T : Ty) (v : Val) (h : FlatTy T v) : HeldOk s v := by
  cases v <;> simp only [HeldOk]
  all_goals first | trivial | (cases T <;> simp [FlatTy] at h)

/-- A type-preserving write keeps the live-reference invariant. -/
theorem liveRefs_write (s s' : Store) (l : Loc) (v : Val) (T : Ty) (hT : T.flat = true)
    (hl : LocTy s l T) (hv : FlatTy T v) (h : s.write l v = .ok s') (hlr : LiveRefs s) :
    LiveRefs s' := by
  obtain ⟨hle, _⟩ := write_le s s' l v T hT hl hv h
  have hm : s.modify l (fun _ => some v) = .ok s' := h
  obtain ⟨old, x, y, new, ho, hx, hy, hmod, hroots⟩ := modify_spec s s' l _ hm
  intro r w hw
  by_cases hrr : r = l.root
  · subst hrr
    have hwn : w = new := by
      rw [hroots] at hw
      simp at hw
      exact hw.symm
    cases hp : l.path with
    | nil =>
      rw [hp] at hmod
      simp [Val.modifyAt?] at hmod
      rw [hwn, ← hmod]
      exact flat_held _ T _ hv
    | cons i q =>
      rw [hwn]
      rw [hp] at hmod
      exact modifyAt_cons_held _ _ _ _ _ _ hmod
  · have h2 : s.roots[r]? = some w := by
      rw [hroots] at hw
      simpa [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Ne.symm hrr] using hw
    exact HeldOk.mono hle (hlr r w h2)


/-- The roots of the variables of block `sc`, instance `si`, in activation `act`. -/
def ScopeRoots (vars : Array LocalVar) (act : ActId) (sc : Nat) (si : ScopeInst) (r : RootInst) : Prop :=
  ∃ x lv, vars[x]? = some lv ∧ lv.scope = sc ∧ r = .local act si x

theorem releaseVars_roots (vars : Array LocalVar) (act : ActId) (sc : Nat) (si : ScopeInst) :
    ∀ (i : Nat) (st : Store) (r : RootInst),
      (releaseVars vars act sc si i st).roots[r]? =
        if (∃ x, x < i ∧ ∃ lv, vars[x]? = some lv ∧ lv.scope = sc ∧ r = .local act si x)
        then none else st.roots[r]? := by
  intro i
  induction i with
  | zero => intro st r; simp [releaseVars]
  | succ i ih =>
    intro st r
    cases hv : vars[i]? with
    | none =>
      simp only [releaseVars, hv]
      rw [ih]
      congr 1
      apply propext
      constructor
      · rintro ⟨x, hx, lv, h1, h2, h3⟩
        exact ⟨x, by omega, lv, h1, h2, h3⟩
      · rintro ⟨x, hx, lv, h1, h2, h3⟩
        have : x ≠ i := by rintro rfl; rw [hv] at h1; cases h1
        exact ⟨x, by omega, lv, h1, h2, h3⟩
    | some lv =>
      simp only [releaseVars, hv]
      by_cases hs : lv.scope = sc
      · simp only [hs, beq_self_eq_true, ite_true]
        rw [ih]
        by_cases hr : r = .local act si i
        · subst hr
          have : ∃ x, x < i + 1 ∧ ∃ lv, vars[x]? = some lv ∧ lv.scope = sc ∧ RootInst.local act si i = .local act si x :=
            ⟨i, by omega, lv, hv, hs, rfl⟩
          have hno : ¬ ∃ x, x < i ∧ ∃ lv, vars[x]? = some lv ∧ lv.scope = sc ∧ RootInst.local act si i = .local act si x := by
            rintro ⟨x, hx, lv', _, _, h3⟩
            simp only [RootInst.local.injEq, true_and] at h3
            subst h3
            exact Nat.lt_irrefl _ hx
          simp only [hno, this, ite_false, ite_true]
          simp [Store.release]
        · have hiff : (∃ x, x < i ∧ ∃ lv, vars[x]? = some lv ∧ lv.scope = sc ∧ r = .local act si x) ↔
              (∃ x, x < i + 1 ∧ ∃ lv, vars[x]? = some lv ∧ lv.scope = sc ∧ r = .local act si x) := by
            constructor
            · rintro ⟨x, hx, lv', h1, h2, h3⟩
              exact ⟨x, by omega, lv', h1, h2, h3⟩
            · rintro ⟨x, hx, lv', h1, h2, h3⟩
              have : x ≠ i := by rintro rfl; exact hr h3
              exact ⟨x, by omega, lv', h1, h2, h3⟩
          simp only [hiff]
          by_cases hex : (∃ x, x < i + 1 ∧ ∃ lv, vars[x]? = some lv ∧ lv.scope = sc ∧ r = .local act si x)
          · simp [hex]
          · simp [hex, Store.release, Std.HashMap.getElem?_erase, Ne.symm hr]
      · have hb : (lv.scope == sc) = false := by simpa using hs
        simp only [hb]
        simp only [Bool.false_eq_true, ite_false]
        rw [ih]
        congr 1
        apply propext
        constructor
        · rintro ⟨x, hx, lv', h1, h2, h3⟩
          exact ⟨x, by omega, lv', h1, h2, h3⟩
        · rintro ⟨x, hx, lv', h1, h2, h3⟩
          have : x ≠ i := by rintro rfl; rw [hv] at h1; cases h1; exact hs h2
          exact ⟨x, by omega, lv', h1, h2, h3⟩


theorem releaseScope_roots (vars : Array LocalVar) (act : ActId) (sc : Nat) (si : ScopeInst)
    (st : Store) :
    (∀ r, ¬ ScopeRoots vars act sc si r →
      (releaseVars vars act sc si vars.size st).roots[r]? = st.roots[r]?) ∧
    (∀ r, ScopeRoots vars act sc si r →
      (releaseVars vars act sc si vars.size st).roots[r]? = none) := by
  have key : ∀ r, (∃ x, x < vars.size ∧ ∃ lv, vars[x]? = some lv ∧ lv.scope = sc ∧ r = .local act si x)
      ↔ ScopeRoots vars act sc si r := by
    intro r
    constructor
    · rintro ⟨x, _, lv, h1, h2, h3⟩; exact ⟨x, lv, h1, h2, h3⟩
    · rintro ⟨x, lv, h1, h2, h3⟩
      exact ⟨x, (Array.getElem?_eq_some_iff.1 h1).1, lv, h1, h2, h3⟩
  constructor
  · intro r hr
    rw [releaseVars_roots]
    have : ¬ (∃ x, x < vars.size ∧ ∃ lv, vars[x]? = some lv ∧ lv.scope = sc ∧ r = .local act si x) :=
      fun h => hr ((key r).1 h)
    simp [this]
  · intro r hr
    rw [releaseVars_roots]
    simp [(key r).2 hr]

/-- A reference or slice that does not target a released root. -/
def TargetsOk (P : RootInst → Prop) : Val → Prop
  | .ref l => ¬ P l.root
  | .slice l _ _ => ¬ P l.root
  | _ => True

theorem read_agree {s s' : Store} {P : RootInst → Prop} {l : Loc} {v : Val}
    (hagree : ∀ r, ¬ P r → s'.roots[r]? = s.roots[r]?) (hl : ¬ P l.root)
    (h : s.read l = .ok v) : s'.read l = .ok v := by
  obtain ⟨old, ho, hg⟩ := (read_ok_iff _ _ _).1 h
  exact (read_ok_iff _ _ _).2 ⟨old, by rw [hagree _ hl]; exact ho, hg⟩

theorem locTy_agree {s s' : Store} {P : RootInst → Prop} {l : Loc} {T : Ty}
    (hagree : ∀ r, ¬ P r → s'.roots[r]? = s.roots[r]?) (hl : ¬ P l.root)
    (h : LocTy s l T) : LocTy s' l T := by
  obtain ⟨v, hv, hT⟩ := h
  exact ⟨v, read_agree hagree hl hv, hT⟩

theorem heldOk_agree {s s' : Store} {P : RootInst → Prop} {v : Val}
    (hagree : ∀ r, ¬ P r → s'.roots[r]? = s.roots[r]?) (ht : TargetsOk P v)
    (h : HeldOk s v) : HeldOk s' v := by
  cases v <;> simp only [HeldOk, TargetsOk] at h ht ⊢
  · obtain ⟨T, hT, hl⟩ := h
    exact ⟨T, hT, locTy_agree hagree ht hl⟩
  · obtain ⟨E, h⟩ := h
    refine ⟨E, ?_⟩
    rcases h with ⟨k, hl, hk⟩ | ⟨hl, E', es, hr, hk⟩
    · exact Or.inl ⟨k, locTy_agree hagree ht hl, hk⟩
    · exact Or.inr ⟨locTy_agree hagree ht hl, E', es, read_agree hagree ht hr, hk⟩

/-- Scope exit keeps the live-reference invariant, given that no reference that
survives targets a root of the scope that ended. -/
theorem liveRefs_release (s s' : Store) (P : RootInst → Prop)
    (hagree : ∀ r, ¬ P r → s'.roots[r]? = s.roots[r]?)
    (hgone : ∀ r, P r → s'.roots[r]? = none)
    (hlr : LiveRefs s)
    (hsurv : ∀ r v, ¬ P r → s.roots[r]? = some v → TargetsOk P v) : LiveRefs s' := by
  intro r v hv
  by_cases hr : P r
  · rw [hgone r hr] at hv; cases hv
  · have h0 : s.roots[r]? = some v := by rw [← hagree r hr]; exact hv
    exact heldOk_agree hagree (hsurv r v hr h0) (hlr r v h0)

/-- A block that releases roots created after `s0` leaves `s0` refined. -/
theorem storeLe_release {s0 s st : Store} (P : RootInst → Prop) (hle : StoreLe s0 s)
    (hagree : ∀ r, ¬ P r → st.roots[r]? = s.roots[r]?)
    (hfresh : ∀ r, P r → s0.roots[r]? = none) : StoreLe s0 st := by
  intro r v hv
  have hr : ¬ P r := fun h => by rw [hfresh r h] at hv; cases hv
  obtain ⟨v', hv', hrf⟩ := hle r v hv
  exact ⟨v', by rw [hagree r hr]; exact hv', hrf⟩

end Goose.Proofs.Memory

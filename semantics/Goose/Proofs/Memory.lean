import Goose.Core.Eval
import Goose.Core.Typing

/-!
Facts about the store: what a typed location is, how a store changes without
invalidating one, and that growth keeps every location valid and every
element it already held.
-/

namespace Goose.Proofs.Memory
open Goose.Core

mutual
/-- Typing of a flat value, which holds no reference and needs no store. -/
def FlatTy : Ty → Val → Prop
  | .int t, .int u _ => t = u
  | .bool, .bool _ => True
  | .arr E k, .fixed es => es.size = k ∧ ∀ (i : Nat) (e : Val), es[i]? = some e → FlatTy E e
  | .grow E, .resizable E' es | .growshrink E, .resizable E' es =>
      E = E' ∧ ∀ (i : Nat) (e : Val), es[i]? = some e → FlatTy E e
  | .limited E capacity, .limited E' capacity' slots len =>
      E = E' ∧ capacity = capacity' ∧ len ≤ capacity ∧ len ≤ slots.size ∧
        ∀ (i : Nat) (e : Val), slots[i]? = some e → FlatTy E e
  | .structT sid ts, .record sid' vs => sid = sid' ∧ FieldsTy ts vs.toList
  | _, _ => False

/-- Each record field has its declaration's type, in real-field order. -/
def FieldsTy : TyList → List Val → Prop
  | .nil, [] => True
  | .cons t ts, v :: vs => FlatTy t v ∧ FieldsTy ts vs
  | _, _ => False
end

theorem fields_get : ∀ (ts : TyList) (vs : List Val), FieldsTy ts vs →
    ∀ (i : Nat) (t : Ty), ts.toList[i]? = some t → ∃ v, vs[i]? = some v ∧ FlatTy t v
  | .nil, vs, h, i, t, ht => by simp [TyList.toList] at ht
  | .cons u us, vs, h, i, t, ht => by
    cases vs with
    | nil => simp [FieldsTy] at h
    | cons v vs =>
      cases i with
      | zero =>
        simp only [TyList.toList, List.getElem?_cons_zero, Option.some.injEq] at ht
        subst ht
        exact ⟨v, by simp, h.1⟩
      | succ i => exact fields_get us vs h.2 i t (by simpa [TyList.toList] using ht)

/-- A field path follows declared nominal fields; it never interprets byte offsets. -/
inductive FieldPath : Ty → List Nat → Ty → Prop
  | root (t : Ty) : FieldPath t [] t
  | field {sid : StructId} {ts : TyList} {i : Nat} {p : List Nat} {t result : Ty}
      (selector : ts.toList[i]? = some t) (rest : FieldPath t p result) :
      FieldPath (.structT sid ts) (i :: p) result

theorem FieldPath.append {a b c : Ty} {p q : List Nat} (h : FieldPath a p b)
    (k : FieldPath b q c) : FieldPath a (p ++ q) c := by
  induction h with
  | root => exact k
  | field selector rest ih => exact .field selector (ih k)

theorem FieldPath.get {root result : Ty} {p : List Nat} (path : FieldPath root p result)
    {v : Val} (h : FlatTy root v) : ∃ w, v.get? p = some w ∧ FlatTy result w := by
  induction path generalizing v with
  | root t => exact ⟨v, rfl, h⟩
  | @field sid ts i p t result selector rest ih =>
    cases v <;> simp only [FlatTy] at h
    rename_i sid' vs
    obtain ⟨e, he, ht⟩ := fields_get _ _ h.2 _ _ selector
    obtain ⟨w, hw, htype⟩ := ih ht
    refine ⟨w, ?_, htype⟩
    simp only [Val.get?, Val.children?]
    have he' : vs[i]? = some e := by simpa using he
    simp only [he', Option.bind_some, hw]

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

theorem get_limited (E : Ty) (capacity : Nat) (slots : Array Val) (len i : Nat)
    (rest : List Nat) :
    (Val.limited E capacity slots len).get? (i :: rest) =
      (slots[i]?).bind (fun e => e.get? rest) := by
  simp [Val.get?, Val.children?, Val.elems?]
  cases slots[i]? <;> rfl


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
  cases T with
  | grow E | growshrink E =>
    simp only [FlatTy] at h ⊢
    rcases h with ⟨rfl, hElems⟩
    refine ⟨rfl, fun j e2 hj => ?_⟩
    rw [Array.getElem?_set] at hj
    split at hj
    · rename_i hij
      cases hj
      subst hij
      exact hT E (hElems i es[i] (Array.getElem?_eq_getElem hi))
    · exact hElems j e2 hj
  | _ => simp [FlatTy] at h ⊢

theorem flat_limited_set (T E0 : Ty) (capacity : Nat) (slots : Array Val) (len i : Nat)
    (hi : i < slots.size) (e' : Val)
    (h : FlatTy T (.limited E0 capacity slots len))
    (hT : ∀ T', FlatTy T' slots[i] → FlatTy T' e') :
    FlatTy T (.limited E0 capacity (slots.set i e' hi) len) := by
  cases T <;> simp only [FlatTy] at h ⊢
  rcases h with ⟨hE, hC, hLenCap, hLenSize, hslots⟩
  cases hE
  refine ⟨rfl, hC, hLenCap, ?_, fun j e2 hj => ?_⟩
  · simpa using hLenSize
  · rw [Array.getElem?_set] at hj
    split at hj
    · rename_i hij
      cases hj
      subst hij
      exact hT E0 (by simpa using hslots i slots[i] (Array.getElem?_eq_getElem hi))
    · exact hslots j e2 hj

theorem flat_limited_truncate (T E : Ty) (capacity : Nat) (slots : Array Val)
    (old len : Nat) (hlen : len ≤ old)
    (h : FlatTy T (.limited E capacity slots old)) :
    FlatTy T (.limited E capacity slots len) := by
  cases T with
  | limited E' capacity' =>
    simp only [FlatTy] at h ⊢
    rcases h with ⟨hE, hcap, hcapacity, hsize, hslots⟩
    exact ⟨hE, hcap, Nat.le_trans hlen hcapacity,
      Nat.le_trans hlen hsize, hslots⟩
  | _ => simp [FlatTy] at h ⊢

theorem flat_resizable_append (T E : Ty) (es vs : Array Val)
    (h : FlatTy T (.resizable E es))
    (hvs : ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e) :
    FlatTy T (.resizable E (es ++ vs)) := by
  cases T with
  | grow E' | growshrink E' =>
    simp only [FlatTy] at h ⊢
    rcases h with ⟨rfl, helem⟩
    refine ⟨rfl, fun i e hi => ?_⟩
    by_cases hleft : i < es.size
    · rw [Array.getElem?_append_left hleft] at hi
      exact helem i e hi
    · rw [Array.getElem?_append_right (by omega)] at hi
      exact hvs (i - es.size) e hi
  | _ => simp [FlatTy] at h ⊢

theorem flat_resizable_extract (T E : Ty) (es : Array Val) (len : Nat)
    (hlen : len ≤ es.size) (h : FlatTy T (.resizable E es)) :
    FlatTy T (.resizable E (es.extract 0 len)) := by
  cases T with
  | grow E' | growshrink E' =>
    simp only [FlatTy] at h ⊢
    rcases h with ⟨rfl, helem⟩
    refine ⟨rfl, fun i e hi => ?_⟩
    rw [Array.getElem?_extract] at hi
    split at hi
    · exact helem i e (by simpa [Nat.zero_add] using hi)
    · cases hi
  | _ => simp [FlatTy] at h ⊢

def limitedAppendSlots (slots vs : Array Val) (len : Nat) : Array Val :=
  let written := slots.extract 0 len ++ vs
  written ++ slots.extract written.size slots.size

theorem appendAll_limited_shape (E : Ty) (capacity : Nat) (slots vs : Array Val) (len : Nat)
    (hlen : len ≤ slots.size) (hcap : len + vs.size ≤ capacity) :
    Val.appendAll vs (.limited E capacity slots len) =
      some (.limited E capacity (limitedAppendSlots slots vs len) (len + vs.size)) := by
  simp [Val.appendAll, hcap, limitedAppendSlots, hlen, Nat.min_eq_left hlen,
    Array.size_append, Array.size_extract, Array.append_assoc]

theorem limitedAppendSlots_written_size (slots vs : Array Val) (len : Nat)
    (hlen : len ≤ slots.size) :
    (slots.extract 0 len ++ vs).size = len + vs.size := by
  simp [Array.size_append, Array.size_extract, Nat.min_eq_left hlen]

theorem limitedAppendSlots_written_le_size (slots vs : Array Val) (len : Nat) :
    (slots.extract 0 len ++ vs).size ≤ (limitedAppendSlots slots vs len).size := by
  unfold limitedAppendSlots
  simp only [Array.size_append]
  omega

theorem limitedAppendSlots_size (slots vs : Array Val) (len : Nat)
    (hlen : len ≤ slots.size) :
    slots.size ≤ (limitedAppendSlots slots vs len).size := by
  unfold limitedAppendSlots
  let written := slots.extract 0 len ++ vs
  have hwritten : written.size = len + vs.size := by
    dsimp [written]
    exact limitedAppendSlots_written_size slots vs len hlen
  simp only [Array.size_append, Array.size_extract, Nat.min_self]
  by_cases hsmall : written.size ≤ slots.size <;> omega

theorem limitedAppendSlots_size_eq (slots vs : Array Val) (len : Nat)
    (hlen : len ≤ slots.size) (hwritten : len + vs.size ≤ slots.size) :
    (limitedAppendSlots slots vs len).size = slots.size := by
  unfold limitedAppendSlots
  simp only [Array.size_append, Array.size_extract, Nat.min_eq_left hlen, Nat.min_self]
  omega

theorem limitedAppendSlots_get_visible (slots vs : Array Val) (len i : Nat)
    (hlen : len ≤ slots.size) (hi : i < len) :
    (limitedAppendSlots slots vs len)[i]? = slots[i]? := by
  have hwritten := limitedAppendSlots_written_size slots vs len hlen
  unfold limitedAppendSlots
  rw [Array.getElem?_append_left (by rw [hwritten]; omega)]
  rw [Array.getElem?_append_left (by simp [Array.size_extract, Nat.min_eq_left hlen]; omega)]
  rw [Array.getElem?_extract]
  simp [Nat.min_eq_left hlen, hi]

theorem limitedAppendSlots_get_appended (slots vs : Array Val) (len i : Nat)
    (hlen : len ≤ slots.size) (hi : i < vs.size) :
    (limitedAppendSlots slots vs len)[len + i]? = vs[i]? := by
  have hwritten := limitedAppendSlots_written_size slots vs len hlen
  unfold limitedAppendSlots
  rw [Array.getElem?_append_left (by rw [hwritten]; omega)]
  rw [Array.getElem?_append_right (by simp [Array.size_extract, Nat.min_eq_left hlen])]
  simp [Array.size_extract, Nat.min_eq_left hlen, Nat.add_sub_cancel_left]

theorem limitedAppendSlots_get_suffix (slots vs : Array Val) (len i : Nat)
    (hlen : len ≤ slots.size) (hi : len + vs.size ≤ i) (his : i < slots.size) :
    (limitedAppendSlots slots vs len)[i]? = slots[i]? := by
  have hwritten := limitedAppendSlots_written_size slots vs len hlen
  have hsmall : (slots.extract 0 len ++ vs).size ≤ slots.size := by rw [hwritten]; omega
  unfold limitedAppendSlots
  rw [Array.getElem?_append_right (by rw [hwritten]; omega)]
  rw [Array.getElem?_extract]
  have hidx : i - (slots.extract 0 len ++ vs).size <
      slots.size - (slots.extract 0 len ++ vs).size := by rw [hwritten]; omega
  have hidx' : i - (slots.extract 0 len ++ vs).size <
      min slots.size slots.size - (slots.extract 0 len ++ vs).size := by
    simpa [Nat.min_self] using hidx
  rw [if_pos hidx']
  congr 1
  omega

theorem flat_limitedAppendSlots (E : Ty) (slots vs : Array Val) (len : Nat)
    (hlen : len ≤ slots.size)
    (hslots : ∀ (i : Nat) (e : Val), slots[i]? = some e → FlatTy E e)
    (hvs : ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e) :
    ∀ (i : Nat) (e : Val), (limitedAppendSlots slots vs len)[i]? = some e → FlatTy E e := by
  intro i e he
  have hwritten_size := (limitedAppendSlots slots vs len).size
  unfold limitedAppendSlots at he
  let written := slots.extract 0 len ++ vs
  by_cases hwritten : i < written.size
  · rw [Array.getElem?_append_left hwritten] at he
    by_cases hprefix : i < (slots.extract 0 len).size
    · rw [Array.getElem?_append_left hprefix] at he
      rw [Array.getElem?_extract] at he
      split at he
      · exact hslots i e (by simpa [Nat.zero_add] using he)
      · cases he
    · rw [Array.getElem?_append_right (by omega)] at he
      have hprefix_size : (slots.extract 0 len).size = len := by
        simp [Array.size_extract, Nat.min_eq_left hlen]
      have he' : vs[i - (slots.extract 0 len).size]? = some e := by simpa using he
      rw [hprefix_size] at he'
      exact hvs _ e (by simpa [written] using he')
  · have hwritten_le : written.size ≤ i := Nat.le_of_not_gt hwritten
    rw [Array.getElem?_append_right (by simpa [written] using hwritten_le)] at he
    rw [Array.getElem?_extract] at he
    split at he
    · exact hslots _ e (by simpa [Nat.add_sub_cancel_left] using he)
    · cases he

theorem flat_limitedAppend (E : Ty) (capacity : Nat) (slots vs : Array Val) (len : Nat)
    (hslots : ∀ (i : Nat) (e : Val), slots[i]? = some e → FlatTy E e)
    (hvs : ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e)
    (hlen : len ≤ slots.size) (hcap : len + vs.size ≤ capacity) (hE : E.flat = true) :
    FlatTy (.limited E capacity)
      (.limited E capacity (limitedAppendSlots slots vs len) (len + vs.size)) := by
  refine ⟨rfl, rfl, hcap, ?_, flat_limitedAppendSlots E slots vs len hlen hslots hvs⟩
  have hsize := limitedAppendSlots_written_le_size slots vs len
  rw [limitedAppendSlots_written_size slots vs len hlen] at hsize
  omega

/-- Replacing the sub-value at a path by one that refines it refines the whole. -/
theorem fields_set : ∀ (ts : TyList) (vs : List Val) (i : Nat) (v' : Val),
    FieldsTy ts vs → (∀ v, vs[i]? = some v → ∀ T, FlatTy T v → FlatTy T v') →
    FieldsTy ts (vs.set i v')
  | .nil, vs, i, v', h, hc => by cases vs <;> simp_all [FieldsTy]
  | .cons t ts, vs, i, v', h, hc => by
    cases vs with
    | nil => simp [FieldsTy] at h
    | cons v vs =>
      simp only [FieldsTy] at h
      cases i with
      | zero => exact ⟨hc v (by simp) t h.1, h.2⟩
      | succ i =>
        exact ⟨h.1, fields_set ts vs i v' h.2 (fun w hw => hc w (by simpa using hw))⟩

theorem flat_record_set (T : Ty) (sid : StructId) (es : Array Val) (i : Nat)
    (hi : i < es.size) (e' : Val) (h : FlatTy T (.record sid es))
    (hc : ∀ T', FlatTy T' es[i] → FlatTy T' e') :
    FlatTy T (.record sid (es.set i e' hi)) := by
  cases T <;> simp only [FlatTy] at h ⊢
  refine ⟨h.1, ?_⟩
  rw [Array.toList_set]
  exact fields_set _ _ i e' h.2 (fun v hv T ht => by
    have he : es[i]? = some v := by simpa using hv
    rw [Array.getElem?_eq_getElem hi] at he
    cases he
    exact hc T ht)

/-- Replacing a nested value preserves every flat type the replacement keeps. -/
theorem flat_modifyAt_type (f : Val → Option Val) :
    ∀ (p : List Nat) (v v' x y : Val), v.modifyAt? p f = some v' →
      v.get? p = some x → f x = some y →
      (∀ T, FlatTy T x → FlatTy T y) →
      ∀ T, FlatTy T v → FlatTy T v' := by
  intro p
  induction p with
  | nil =>
    intro v v' x y hmod hget hwrite htypes T hflat
    simp [Val.modifyAt?] at hmod
    simp [Val.get?] at hget
    subst hget
    rw [hwrite] at hmod
    cases hmod
    exact htypes T hflat
  | cons i rest ih =>
    intro v v' x y hmod hget hwrite htypes T hflat
    cases v with
    | fixed es =>
      simp only [Val.modifyAt?] at hmod
      split at hmod
      · rename_i hi
        split at hmod
        · rename_i e' he'
          cases hmod
          rw [get_fixed, Array.getElem?_eq_getElem hi] at hget
          simp only [Option.bind_some] at hget
          have hchild : ∀ U, FlatTy U es[i] → FlatTy U e' := by
            intro U hU
            exact ih es[i] e' x y he' hget hwrite htypes U hU
          exact flat_fixed_set T es i hi e' hflat hchild
        · simp at hmod
      · simp at hmod
    | record sid es =>
      simp only [Val.modifyAt?] at hmod
      split at hmod
      · rename_i hi
        split at hmod
        · rename_i e' he'
          cases hmod
          rw [get_record, Array.getElem?_eq_getElem hi] at hget
          simp only [Option.bind_some] at hget
          have hchild : ∀ U, FlatTy U es[i] → FlatTy U e' := by
            intro U hU
            exact ih es[i] e' x y he' hget hwrite htypes U hU
          exact flat_record_set T sid es i hi e' hflat hchild
        · simp at hmod
      · simp at hmod
    | resizable E es =>
      simp only [Val.modifyAt?] at hmod
      split at hmod
      · rename_i hi
        split at hmod
        · rename_i e' he'
          cases hmod
          rw [get_resizable, Array.getElem?_eq_getElem hi] at hget
          simp only [Option.bind_some] at hget
          have hchild : ∀ U, FlatTy U es[i] → FlatTy U e' := by
            intro U hU
            exact ih es[i] e' x y he' hget hwrite htypes U hU
          exact flat_resizable_set T E es i hi e' hflat hchild
        · simp at hmod
      · simp at hmod
    | limited E capacity slots len =>
      simp only [Val.modifyAt?] at hmod
      split at hmod
      · rename_i hi
        split at hmod
        · rename_i e' he'
          cases hmod
          rw [get_limited, Array.getElem?_eq_getElem hi] at hget
          simp only [Option.bind_some] at hget
          have hchild : ∀ U, FlatTy U slots[i] → FlatTy U e' := by
            intro U hU
            exact ih slots[i] e' x y he' hget hwrite htypes U hU
          exact flat_limited_set T E capacity slots len i hi e' hflat hchild
        · simp at hmod
      · simp at hmod
    | _ => simp [Val.modifyAt?] at hmod

/-- A successful update below a prefix is the same update inside that prefix. -/
theorem modifyAt_prefix_decompose (f : Val → Option Val) :
    ∀ (pre suffix : List Nat) (v v' : Val),
      v.modifyAt? (pre ++ suffix) f = some v' →
      ∃ x y, v.get? pre = some x ∧ v'.get? pre = some y ∧
        x.modifyAt? suffix f = some y := by
  intro pre
  induction pre with
  | nil =>
    intro suffix v v' hmod
    simp only [List.nil_append] at hmod
    exact ⟨v, v', by simp [get_nil], by simp [get_nil], hmod⟩
  | cons i rest ih =>
    intro suffix v v' hmod
    cases v with
    | fixed es =>
      simp only [List.cons_append, Val.modifyAt?] at hmod
      split at hmod
      · rename_i hi
        split at hmod
        · rename_i child' hchild
          cases hmod
          obtain ⟨x, y, hx, hy, hupdate⟩ := ih suffix es[i] child' hchild
          refine ⟨x, y, ?_, ?_, hupdate⟩
          · rw [get_fixed, Array.getElem?_eq_getElem hi]
            simpa using hx
          · rw [get_fixed, Array.getElem?_set_self hi]
            simpa using hy
        · simp at hmod
      · simp at hmod
    | record sid es =>
      simp only [List.cons_append, Val.modifyAt?] at hmod
      split at hmod
      · rename_i hi
        split at hmod
        · rename_i child' hchild
          cases hmod
          obtain ⟨x, y, hx, hy, hupdate⟩ := ih suffix es[i] child' hchild
          refine ⟨x, y, ?_, ?_, hupdate⟩
          · rw [get_record, Array.getElem?_eq_getElem hi]
            simpa using hx
          · rw [get_record, Array.getElem?_set_self hi]
            simpa using hy
        · simp at hmod
      · simp at hmod
    | resizable E es =>
      simp only [List.cons_append, Val.modifyAt?] at hmod
      split at hmod
      · rename_i hi
        split at hmod
        · rename_i child' hchild
          cases hmod
          obtain ⟨x, y, hx, hy, hupdate⟩ := ih suffix es[i] child' hchild
          refine ⟨x, y, ?_, ?_, hupdate⟩
          · rw [get_resizable, Array.getElem?_eq_getElem hi]
            simpa using hx
          · rw [get_resizable, Array.getElem?_set_self hi]
            simpa using hy
        · simp at hmod
      · simp at hmod
    | limited E capacity slots len =>
      simp only [List.cons_append, Val.modifyAt?] at hmod
      split at hmod
      · rename_i hi
        split at hmod
        · rename_i child' hchild
          cases hmod
          obtain ⟨x, y, hx, hy, hupdate⟩ := ih suffix slots[i] child' hchild
          refine ⟨x, y, ?_, ?_, hupdate⟩
          · rw [get_limited, Array.getElem?_eq_getElem hi]
            simpa using hx
          · rw [get_limited, Array.getElem?_set_self hi]
            simpa using hy
        · simp at hmod
      · simp at hmod
    | _ => simp [Val.modifyAt?] at hmod

/-- Updating below the root of an array keeps that array's element count. -/
theorem modifyAt_nonempty_preserves_elems_size (f : Val → Option Val) :
    ∀ (i : Nat) (p : List Nat) (v v' : Val),
      v.modifyAt? (i :: p) f = some v' →
      ∀ es, v.elems? = some es →
        ∃ es', v'.elems? = some es' ∧ es'.size = es.size := by
  intro i p v v' hmod es helems
  cases v with
  | fixed old =>
    simp only [Val.modifyAt?] at hmod
    split at hmod
    · rename_i hi
      split at hmod
      · rename_i child' hchild
        cases hmod
        simp only [Val.elems?, Option.some.injEq] at helems
        subst es
        exact ⟨old.set i child', by simp [Val.elems?], by simp⟩
      · simp at hmod
    · simp at hmod
  | resizable E old =>
    simp only [Val.modifyAt?] at hmod
    split at hmod
    · rename_i hi
      split at hmod
      · rename_i child' hchild
        cases hmod
        simp only [Val.elems?, Option.some.injEq] at helems
        subst es
        exact ⟨old.set i child', by simp [Val.elems?], by simp⟩
      · simp at hmod
    · simp at hmod
  | limited E capacity old len =>
    simp only [Val.modifyAt?] at hmod
    split at hmod
    · rename_i hi
      split at hmod
      · rename_i child' hchild
        cases hmod
        simp only [Val.elems?, Option.some.injEq] at helems
        subst es
        exact ⟨old.set i child', by simp [Val.elems?], by simp⟩
      · simp at hmod
    · simp at hmod
  | _ => simp [Val.elems?] at helems

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
            · exact fun T hT => flat_record_set T sid es i hi _ hT hT0
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
    | limited E0 capacity slots len =>
      simp only [Val.modifyAt?] at h1
      split at h1
      · rename_i hi
        split at h1
        · rename_i e' he'
          cases h1
          rw [get_limited, Array.getElem?_eq_getElem hi] at h2
          simp only [Option.bind_some] at h2
          have hr := ih slots[i] e' x y he' h2 h3 h4
          have hr0 := hr [] slots[i] (get_nil _)
          obtain ⟨x0, hx0, hT0, hs0⟩ := hr0
          rw [get_nil] at hx0; cases hx0
          intro q w hq
          cases q with
          | nil =>
            rw [get_nil] at hq; cases hq
            refine ⟨_, get_nil _,
              fun T hT => flat_limited_set T E0 capacity slots len i hi _ hT hT0,
              fun es' hes' => ?_⟩
            simp only [Val.elems?, Option.some.injEq] at hes'
            subst hes'
            exact ⟨_, rfl, by simp⟩
          | cons j q' =>
            rw [get_limited] at hq
            rw [get_limited]
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

/-- Roots outside `skip` keep their exact stored values across a local rewrite. -/
def StoreLeExcept (skip : RootInst → Prop) (s s' : Store) : Prop :=
  ∀ r, ¬ skip r → s'.roots[r]? = s.roots[r]?

theorem StoreLeExcept.trans {P : RootInst → Prop} {s₁ s₂ s₃ : Store}
    (h₁ : StoreLeExcept P s₁ s₂) (h₂ : StoreLeExcept P s₂ s₃) :
    StoreLeExcept P s₁ s₃ := by
  intro r hr
  rw [h₂ r hr, h₁ r hr]

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

theorem LocTy.mono_except {s s' : Store} {l : Loc} {T : Ty} {P : RootInst → Prop}
    (hagree : StoreLeExcept P s s') (hnot : ¬ P l.root) (h : LocTy s l T) :
    LocTy s' l T := by
  obtain ⟨v, hv, hT⟩ := h
  obtain ⟨old, ho, hg⟩ := (read_ok_iff _ _ _).1 hv
  exact ⟨v, (read_ok_iff _ _ _).2 ⟨old, by rw [hagree l.root hnot]; exact ho, hg⟩, hT⟩

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
    | limited E0 capacity slots len =>
      simp only [Val.modifyAt?] at h1
      split at h1
      · rename_i hi
        split at h1
        · rename_i e' he'
          rw [get_limited, Array.getElem?_eq_getElem hi] at h2
          simp only [Option.bind_some] at h2
          exact ih slots[i] e' x he' h2
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

theorem modify_roots_agree_except (s s' : Store) (l : Loc) (f : Val → Option Val)
    (h : s.modify l f = .ok s') : StoreLeExcept (fun r => r = l.root) s s' := by
  obtain ⟨old, x, y, new, ho, hx, hy, hmod, hroots⟩ := modify_spec s s' l f h
  intro r hr
  rw [hroots]
  have hne : l.root ≠ r := fun he => hr he.symm
  simp [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, hne]

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


mutual
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
  | .structT sid ts, hf, x, y, T', hx, hy, hx' => by
    cases x <;> cases y <;> simp only [FlatTy] at hx hy
    rename_i xid xs yid ys
    cases T' <;> simp only [FlatTy] at hx' ⊢
    exact ⟨hx'.1.trans (hx.1.symm.trans hy.1),
      fields_swap ts (by simpa [Ty.flat] using hf) xs.toList ys.toList _ hx.2 hy.2 hx'.2⟩
  | .unit, hf, _, _, _, _, _, _ => by simp [Ty.flat] at hf
  | .grow _, hf, _, _, _, _, _, _ => by simp [Ty.flat] at hf
  | .ref _ _, hf, _, _, _, _, _, _ => by simp [Ty.flat] at hf
  | .slice _ _, hf, _, _, _, _, _, _ => by simp [Ty.flat] at hf
  | .tuple _, hf, _, _, _, _, _, _ => by simp [Ty.flat] at hf


theorem fields_swap : ∀ (ts : TyList), ts.flat = true → ∀ (xs ys : List Val) (us : TyList),
    FieldsTy ts xs → FieldsTy ts ys → FieldsTy us xs → FieldsTy us ys
  | .nil, _, xs, ys, us, hx, hy, hu => by
    cases xs <;> cases ys <;> simp only [FieldsTy] at hx hy
    exact hu
  | .cons t ts, hf, xs, ys, us, hx, hy, hu => by
    cases xs <;> cases ys <;> simp only [FieldsTy] at hx hy
    cases us <;> simp only [FieldsTy] at hu ⊢
    simp only [TyList.flat, Bool.and_eq_true] at hf
    exact ⟨flat_swap t hf.1 _ _ _ hx.1 hy.1 hu.1,
      fields_swap ts hf.2 _ _ _ hx.2 hy.2 hu.2⟩
end

mutual


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
  | .structT sid ts, hf, x, y, hx, hy => by
    cases x <;> cases y <;> simp only [FlatTy] at hx hy
    rename_i xid xs yid ys
    intro p x0 hp
    cases p with
    | nil =>
      rw [get_nil] at hp; cases hp
      refine ⟨_, get_nil _, fun T' h => flat_swap _ hf _ _ T' (by simpa [FlatTy] using hx) (by simpa [FlatTy] using hy) h, ?_⟩
      intro es hes; simp [Val.elems?] at hes
    | cons i q =>
      rw [get_record] at hp
      cases he : xs[i]? with
      | none => simp [he] at hp
      | some e =>
        simp only [he, Option.bind_some] at hp
        obtain ⟨e', he', hr⟩ := fields_refines ts (by simpa [Ty.flat] using hf)
          xs.toList ys.toList hx.2 hy.2 i e (by simpa using he)
        obtain ⟨z, hz, ht, hs⟩ := hr q x0 hp
        refine ⟨z, ?_, ht, hs⟩
        rw [get_record]
        have hh : ys[i]? = some e' := by simpa using he'
        simp only [hh, Option.bind_some]; exact hz
  | .unit, hf, _, _, _, _ => by simp [Ty.flat] at hf
  | .grow _, hf, _, _, _, _ => by simp [Ty.flat] at hf
  | .ref _ _, hf, _, _, _, _ => by simp [Ty.flat] at hf
  | .slice _ _, hf, _, _, _, _ => by simp [Ty.flat] at hf
  | .tuple _, hf, _, _, _, _ => by simp [Ty.flat] at hf


theorem fields_refines : ∀ (ts : TyList), ts.flat = true → ∀ (xs ys : List Val),
    FieldsTy ts xs → FieldsTy ts ys → ∀ (i : Nat) (v : Val), xs[i]? = some v →
    ∃ w, ys[i]? = some w ∧ Refines v w
  | .nil, _, xs, ys, hx, hy, i, v, hv => by
    cases xs <;> simp [FieldsTy] at hx hv
  | .cons t ts, hf, xs, ys, hx, hy, i, v, hv => by
    cases xs <;> cases ys <;> simp only [FieldsTy] at hx hy
    simp only [TyList.flat, Bool.and_eq_true] at hf
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
      subst hv
      exact ⟨_, by simp, flat_refines t hf.1 _ _ hx.1 hy.1⟩
    | succ i =>
      exact fields_refines ts hf.2 _ _ hx.2 hy.2 i v (by simpa using hv)
end

theorem refines_limitedAppend (E : Ty) (capacity : Nat) (slots vs : Array Val) (len : Nat)
    (hslots : ∀ (i : Nat) (e : Val), slots[i]? = some e → FlatTy E e)
    (hvs : ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e)
    (hlen : len ≤ slots.size) (hcap : len + vs.size ≤ capacity) (hE : E.flat = true) :
    Refines (.limited E capacity slots len)
      (.limited E capacity (limitedAppendSlots slots vs len) (len + vs.size)) := by
  intro p
  induction p with
  | nil =>
    intro x hx
    rw [get_nil] at hx
    cases hx
    refine ⟨_, get_nil _, ?_, ?_⟩
    · intro T hT
      cases T <;> simp only [FlatTy] at hT ⊢
      rcases hT with ⟨hE', hcap', hlen', hsize', hslots'⟩
      cases hE'
      cases hcap'
      exact flat_limitedAppend E capacity slots vs len hslots' hvs hlen hcap hE
    · intro es he
      simp only [Val.elems?, Option.some.injEq] at he
      cases he
      exact ⟨limitedAppendSlots slots vs len, rfl, limitedAppendSlots_size slots vs len hlen⟩
  | cons i rest ih =>
    intro x hx
    rw [get_limited] at hx
    cases hslot : slots[i]? with
    | none => simp [hslot] at hx
    | some old =>
      simp only [hslot, Option.bind_some] at hx
      have hold : FlatTy E old := hslots i old hslot
      have hnew : ∃ new, (limitedAppendSlots slots vs len)[i]? = some new ∧ Refines old new := by
        by_cases hi : i < len
        · refine ⟨old, ?_, Refines.refl old⟩
          rw [limitedAppendSlots_get_visible slots vs len i hlen hi, hslot]
        · by_cases hi' : i < len + vs.size
          · have hidx : i - len < vs.size := by omega
            have hslot' : (limitedAppendSlots slots vs len)[i]? = vs[i - len]? := by
              calc
                _ = (limitedAppendSlots slots vs len)[len + (i - len)]? := by congr 1 <;> omega
                _ = vs[i - len]? := limitedAppendSlots_get_appended slots vs len (i - len) hlen hidx
            let new := vs[i - len]
            have hv : vs[i - len]? = some new := Array.getElem?_eq_getElem hidx
            have hnew : (limitedAppendSlots slots vs len)[i]? = some new := hslot'.trans hv
            have hnewTy : FlatTy E new := hvs _ new hv
            exact ⟨new, hnew, flat_refines E hE old new hold hnewTy⟩
          · have hslot' : (limitedAppendSlots slots vs len)[i]? = slots[i]? :=
              limitedAppendSlots_get_suffix slots vs len i hlen (by omega) (Array.getElem?_eq_some_iff.1 hslot |>.1)
            rw [hslot] at hslot'
            exact ⟨old, hslot', Refines.refl old⟩
      obtain ⟨new, hnew, hrefines⟩ := hnew
      rw [get_limited, hnew]
      obtain ⟨x', hx', hty, hsize⟩ := hrefines rest x hx
      exact ⟨x', by simpa using hx', hty, hsize⟩

theorem refines_limitedTruncate (E : Ty) (capacity : Nat) (slots : Array Val)
    (old len : Nat) (hlen : len ≤ old) :
    Refines (.limited E capacity slots old) (.limited E capacity slots len) := by
  intro p
  induction p with
  | nil =>
    intro x hx
    rw [get_nil] at hx
    cases hx
    refine ⟨_, get_nil _, ?_, ?_⟩
    · intro T hT
      exact flat_limited_truncate T E capacity slots old len hlen hT
    · intro es hes
      simp only [Val.elems?, Option.some.injEq] at hes
      cases hes
      exact ⟨slots, rfl, Nat.le_refl _⟩
  | cons i rest ih =>
    intro x hx
    rw [get_limited] at hx ⊢
    cases hslot : slots[i]? with
    | none => simp [hslot] at hx
    | some e =>
      simp only [hslot, Option.bind_some] at hx ⊢
      exact ⟨x, hx, fun _ hT => hT, fun es hes => ⟨es, hes, Nat.le_refl _⟩⟩


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
    refine ⟨_, get_nil _, (fun T' hT' => flat_resizable_append T' E es vs hT' hvs),
      fun es' hes' => ?_⟩
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
    rcases v with _|_|_|es|⟨sid, fields⟩|⟨E, es⟩|⟨E, capacity, slots, len⟩|_|_
    all_goals simp [Val.get?, Val.children?, Val.elems?]
    · cases es[i]? <;> simp [ih]
    · cases fields[i]? <;> simp [ih]
    · cases es[i]? <;> simp [ih]
    · cases slots[i]? <;> simp [ih]

theorem read_resizableElem_iff {s : Store} {l : Loc} {E : Ty} {es : Array Val}
    {i : Nat} {v : Val} (howner : s.read l = .ok (.resizable E es)) :
    s.read ⟨l.root, l.path ++ [i]⟩ = .ok v ↔ es[i]? = some v := by
  constructor
  · intro h
    obtain ⟨ownerRoot, hroot, hgetOwner⟩ := (read_ok_iff _ _ _).1 howner
    obtain ⟨slotRoot, hslotRoot, hgetSlot⟩ := (read_ok_iff _ _ _).1 h
    have hroots : ownerRoot = slotRoot :=
      Option.some.inj (hroot.symm.trans hslotRoot)
    subst slotRoot
    rw [get_append, hgetOwner] at hgetSlot
    simp only [Option.bind_some, get_resizable] at hgetSlot
    cases he : es[i]? with
    | none => simp [he] at hgetSlot
    | some x =>
      simp only [he, Option.bind_some, get_nil] at hgetSlot
      cases hgetSlot
      rfl
  · intro hi
    obtain ⟨ownerRoot, hroot, hgetOwner⟩ := (read_ok_iff _ _ _).1 howner
    apply (read_ok_iff _ _ _).2
    refine ⟨ownerRoot, hroot, ?_⟩
    rw [get_append, hgetOwner]
    simp [get_resizable, hi, get_nil]

theorem read_limitedElem_iff {s : Store} {l : Loc} {E : Ty} {capacity : Nat}
    {slots : Array Val} {len i : Nat} {v : Val}
    (howner : s.read l = .ok (.limited E capacity slots len)) :
    s.read ⟨l.root, l.path ++ [i]⟩ = .ok v ↔ slots[i]? = some v := by
  constructor
  · intro h
    obtain ⟨ownerRoot, hroot, hgetOwner⟩ := (read_ok_iff _ _ _).1 howner
    obtain ⟨slotRoot, hslotRoot, hgetSlot⟩ := (read_ok_iff _ _ _).1 h
    have hroots : ownerRoot = slotRoot :=
      Option.some.inj (hroot.symm.trans hslotRoot)
    subst slotRoot
    rw [get_append, hgetOwner] at hgetSlot
    simp only [Option.bind_some, get_limited] at hgetSlot
    cases he : slots[i]? with
    | none => simp [he] at hgetSlot
    | some x =>
      simp only [he, Option.bind_some, get_nil] at hgetSlot
      cases hgetSlot
      rfl
  · intro hi
    obtain ⟨ownerRoot, hroot, hgetOwner⟩ := (read_ok_iff _ _ _).1 howner
    apply (read_ok_iff _ _ _).2
    refine ⟨ownerRoot, hroot, ?_⟩
    rw [get_append, hgetOwner]
    simp [get_limited, hi, get_nil]

theorem LocTy.fieldPath {s : Store} {l : Loc} {a b : Ty} {p : List Nat}
    (h : LocTy s l a) (k : FieldPath a p b) : LocTy s ⟨l.root, l.path ++ p⟩ b := by
  obtain ⟨v, hv, ht⟩ := h
  obtain ⟨w, hw, hb⟩ := k.get ht
  obtain ⟨root, hr, hg⟩ := (read_ok_iff _ _ _).1 hv
  refine ⟨w, ?_, hb⟩
  apply (read_ok_iff _ _ _).2
  refine ⟨root, hr, ?_⟩
  rw [get_append, hg]
  exact hw

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
    | limited E0 capacity slots len =>
      simp only [Val.modifyAt?] at h1
      split at h1
      · rename_i hi
        split at h1
        · rename_i e' he'
          cases h1
          rw [get_limited, Array.getElem?_eq_getElem hi] at h2
          simp only [Option.bind_some] at h2
          rw [get_limited, Array.getElem?_set_self hi]
          simpa using ih slots[i] e' x y he' h2 h3
        · simp at h1
      · simp at h1
    | _ => simp [Val.modifyAt?] at h1


theorem write_read (s s' : Store) (l : Loc) (v : Val)
    (hwrite : s.write l v = .ok s') : s'.read l = .ok v := by
  have hmodify : s.modify l (fun _ => some v) = .ok s' := by
    simpa [Store.write] using hwrite
  obtain ⟨old, x, y, new, hroot, hget, hnew, hmod, hroots⟩ :=
    modify_spec s s' l (fun _ => some v) hmodify
  have hread := modifyAt_get_same (fun _ => some v) l.path old new x v hmod hget (by simp)
  rw [read_ok_iff]
  exact ⟨new, by rw [hroots]; simp, hread⟩

theorem length_ok (s : Store) (l : Loc) (n : Nat) (h : s.length l = .ok n) :
    (∃ E es, s.read l = .ok (.resizable E es) ∧ n = es.size) ∨
    (∃ E capacity slots len, s.read l = .ok (.limited E capacity slots len) ∧ n = len) := by
  unfold Store.length at h
  cases hr : s.read l with
  | error k => simp [hr] at h
  | ok v =>
    cases v with
    | resizable E es =>
      simp [hr] at h
      exact Or.inl ⟨E, es, rfl, h.symm⟩
    | limited E capacity slots len =>
      simp [hr] at h
      exact Or.inr ⟨E, capacity, slots, len, rfl, h.symm⟩
    | _ => simp [hr] at h

theorem append_spec (s s' : Store) (l : Loc) (vs : Array Val) (n : Nat)
    (h : s.append l vs = .ok (s', n)) :
    (∃ E es, s.read l = .ok (.resizable E es) ∧ n = es.size ∧
      s.modify l (Val.appendAll vs) = .ok s') ∨
    (∃ E capacity slots len, s.read l = .ok (.limited E capacity slots len) ∧ n = len ∧
      s.modify l (Val.appendAll vs) = .ok s') := by
  unfold Store.append at h
  cases hl : s.length l with
  | error k => simp [hl] at h
  | ok n0 =>
    simp only [hl] at h
    cases hm : s.modify l (Val.appendAll vs) with
    | error k => simp [hm] at h
    | ok s1 =>
      have hp : s1 = s' ∧ n0 = n := by simpa [hl, hm] using h
      rcases hp with ⟨rfl, rfl⟩
      rcases length_ok s l n0 hl with hres | hlimited
      · obtain ⟨E, es, hread, hn⟩ := hres
        exact Or.inl ⟨E, es, hread, hn, rfl⟩
      · obtain ⟨E, capacity, slots, len, hread, hn⟩ := hlimited
        exact Or.inr ⟨E, capacity, slots, len, hread, hn, rfl⟩

theorem append_spec_grow (s s' : Store) (l : Loc) (vs : Array Val) (n : Nat) (E : Ty)
    (hl : LocTy s l (.grow E)) (h : s.append l vs = .ok (s', n)) :
    ∃ es, s.read l = .ok (.resizable E es) ∧ n = es.size ∧
      s.modify l (Val.appendAll vs) = .ok s' := by
  rcases append_spec s s' l vs n h with hres | hlimited
  · obtain ⟨E1, es, hr, hn, hm⟩ := hres
    have hE : E = E1 := by
      obtain ⟨x, hx, hT⟩ := hl
      rw [hr] at hx; cases hx
      simpa [FlatTy] using hT.1
    subst E1
    exact ⟨es, hr, hn, hm⟩
  · obtain ⟨E1, capacity, slots, len, hr, _, _⟩ := hlimited
    obtain ⟨x, hx, hT⟩ := hl
    rw [hr] at hx; cases hx
    simp [FlatTy] at hT

theorem append_spec_growshrink (s s' : Store) (l : Loc) (vs : Array Val) (n : Nat) (E : Ty)
    (hl : LocTy s l (.growshrink E)) (h : s.append l vs = .ok (s', n)) :
    ∃ es, s.read l = .ok (.resizable E es) ∧ n = es.size ∧
      s.modify l (Val.appendAll vs) = .ok s' := by
  rcases append_spec s s' l vs n h with hres | hlimited
  · obtain ⟨E1, es, hr, hn, hm⟩ := hres
    have hE : E = E1 := by
      obtain ⟨x, hx, hT⟩ := hl
      rw [hr] at hx; cases hx
      simpa [FlatTy] using hT.1
    subst E1
    exact ⟨es, hr, hn, hm⟩
  · obtain ⟨E1, capacity, slots, len, hr, _, _⟩ := hlimited
    obtain ⟨x, hx, hT⟩ := hl
    rw [hr] at hx; cases hx
    simp [FlatTy] at hT

/-- `TH-MEM-01` store-level core: growth keeps every typed location typed, keeps
every sub-value that existed, and the new elements are read where expected. -/
theorem append_le (s s' : Store) (l : Loc) (vs : Array Val) (n : Nat) (E : Ty)
    (hl : LocTy s l (.grow E)) (hvs : ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e)
    (h : s.append l vs = .ok (s', n)) :
    StoreLe s s' ∧ LocTy s' l (.grow E) ∧
      ∃ es, s.read l = .ok (.resizable E es) ∧ n = es.size ∧
        ∀ (i : Nat) (e : Val), vs[i]? = some e →
          s'.read ⟨l.root, l.path ++ [n + i]⟩ = .ok e := by
  obtain ⟨es, hr, hn, hm⟩ := append_spec_grow s s' l vs n E hl h
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

theorem append_le_growshrink (s s' : Store) (l : Loc) (vs : Array Val) (n : Nat) (E : Ty)
    (hl : LocTy s l (.growshrink E)) (hvs : ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e)
    (h : s.append l vs = .ok (s', n)) :
    StoreLe s s' ∧ LocTy s' l (.growshrink E) ∧
      ∃ es, s.read l = .ok (.resizable E es) ∧ n = es.size ∧
        ∀ (i : Nat) (e : Val), vs[i]? = some e →
          s'.read ⟨l.root, l.path ++ [n + i]⟩ = .ok e := by
  obtain ⟨es, hr, hn, hm⟩ := append_spec_growshrink s s' l vs n E hl h
  have hle : StoreLe s s' := by
    apply modify_le s s' l _ hm
    intro old x0 y ho hx0 hxy
    obtain ⟨old1, ho1, hg1⟩ := (read_ok_iff _ _ _).1 hr
    rw [ho] at ho1; cases ho1
    rw [hx0] at hg1; cases hg1
    simp only [Val.appendAll, Option.some.injEq] at hxy
    subst hxy
    exact refines_push E es vs hvs
  have hnew : LocTy s' l (.growshrink E) := LocTy.mono hle hl
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

theorem append_spec_limited (s s' : Store) (l : Loc) (vs : Array Val) (n : Nat)
    (E : Ty) (capacity : Nat) (hE : E.flat = true)
    (hl : LocTy s l (.limited E capacity))
    (hvs : ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e)
    (h : s.append l vs = .ok (s', n)) :
    ∃ slots len, s.read l = .ok (.limited E capacity slots len) ∧ n = len ∧
      len ≤ slots.size ∧ (∀ (i : Nat) (e : Val), slots[i]? = some e → FlatTy E e) ∧
      len + vs.size ≤ capacity ∧ s.modify l (Val.appendAll vs) = .ok s' := by
  rcases append_spec s s' l vs n h with hres | hlimited
  · obtain ⟨E1, es, hr, _, _⟩ := hres
    obtain ⟨x, hx, hT⟩ := hl
    rw [hr] at hx
    cases hx
    simp [FlatTy] at hT
  · obtain ⟨E1, capacity1, slots, len, hr, hn, hm⟩ := hlimited
    obtain ⟨x, hx, hT⟩ := hl
    rw [hr] at hx
    cases hx
    simp only [FlatTy] at hT
    rcases hT with ⟨hE1, hcap1, hlenCap, hlenSlots, hslots⟩
    cases hE1
    cases hcap1
    obtain ⟨old, x, y, new, ho, hget, hy, hmod, _⟩ :=
      modify_spec s s' l (Val.appendAll vs) hm
    have hxval : x = .limited E capacity slots len := by
      obtain ⟨old1, ho1, hg1⟩ := (read_ok_iff _ _ _).1 hr
      rw [ho] at ho1
      cases ho1
      rw [hget] at hg1
      cases hg1
      rfl
    rw [hxval] at hy
    have hcap : len + vs.size ≤ capacity := by
      simp only [Val.appendAll] at hy
      split at hy
      · assumption
      · simp at hy
    have hshape := appendAll_limited_shape E capacity slots vs len hlenSlots hcap
    rw [hshape] at hy
    cases hy
    exact ⟨slots, len, hr, hn, hlenSlots, hslots, hcap, hm⟩

theorem append_le_limited (s s' : Store) (l : Loc) (vs : Array Val) (n : Nat)
    (E : Ty) (capacity : Nat) (hE : E.flat = true)
    (hl : LocTy s l (.limited E capacity))
    (hvs : ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e)
    (h : s.append l vs = .ok (s', n)) :
    StoreLe s s' ∧ LocTy s' l (.limited E capacity) ∧
      ∃ slots len, s.read l = .ok (.limited E capacity slots len) ∧ n = len ∧
        len ≤ slots.size ∧ len + vs.size ≤ capacity ∧
        (∀ (i : Nat) (e : Val), vs[i]? = some e →
          s'.read ⟨l.root, l.path ++ [len + i]⟩ = .ok e) ∧
        (∀ (i : Nat) (e : Val), i < len → slots[i]? = some e →
          s'.read ⟨l.root, l.path ++ [i]⟩ = .ok e) := by
  obtain ⟨slots, len, hr, hn, hlen, hslots, hcap, hm⟩ :=
    append_spec_limited s s' l vs n E capacity hE hl hvs h
  have hle : StoreLe s s' := by
    apply modify_le s s' l _ hm
    intro old x y ho hx hxy
    obtain ⟨old1, ho1, hg1⟩ := (read_ok_iff _ _ _).1 hr
    rw [ho] at ho1; cases ho1
    rw [hx] at hg1
    have hxval : x = .limited E capacity slots len := by cases hg1; rfl
    subst x
    have hshape := appendAll_limited_shape E capacity slots vs len hlen hcap
    rw [hshape] at hxy
    cases hxy
    exact refines_limitedAppend E capacity slots vs len hslots hvs hlen hcap hE
  obtain ⟨old, x, y, new, ho, hx, hy, hmod, hroots⟩ :=
    modify_spec s s' l (Val.appendAll vs) hm
  obtain ⟨old1, ho1, hg1⟩ := (read_ok_iff _ _ _).1 hr
  rw [ho] at ho1; cases ho1
  rw [hx] at hg1
  have hxval : x = .limited E capacity slots len := by cases hg1; rfl
  subst x
  have hshape := appendAll_limited_shape E capacity slots vs len hlen hcap
  rw [hshape] at hy
  cases hy
  have hgetOwner := modifyAt_get_same (Val.appendAll vs) l.path old new
    (.limited E capacity slots len) (.limited E capacity (limitedAppendSlots slots vs len) (len + vs.size))
    hmod hx hshape
  refine ⟨hle, LocTy.mono hle hl, slots, len, hr, hn, hlen, hcap, ?_, ?_⟩
  · intro i e he
    rw [read_ok_iff]
    refine ⟨new, ?_, ?_⟩
    · rw [hroots]; simp
    · rw [get_append, hgetOwner]
      simp only [Option.bind_some]
      rw [get_limited, limitedAppendSlots_get_appended slots vs len i hlen (Array.getElem?_eq_some_iff.1 he |>.1), he]
      simp [get_nil]
  · intro i e hi he
    rw [read_ok_iff]
    refine ⟨new, ?_, ?_⟩
    · rw [hroots]; simp
    · rw [get_append, hgetOwner]
      simp only [Option.bind_some]
      rw [get_limited, limitedAppendSlots_get_visible slots vs len i hlen hi, he]
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
    | limited E0 capacity slots len =>
      simp only [Val.modifyAt?] at h1
      split at h1
      · rename_i hi
        split at h1
        · rename_i e' he'
          cases h1
          rw [get_limited, Array.getElem?_eq_getElem hi] at h2
          simp only [Option.bind_some] at h2
          cases q with
          | nil =>
            refine ⟨fun hn => absurd (List.nil_prefix) hn, fun _ => ⟨_, get_nil _⟩⟩
          | cons j q' =>
            rw [get_limited] at hq
            rw [get_limited]
            by_cases hij : i = j
            · subst hij
              rw [Array.getElem?_eq_getElem hi] at hq
              simp only [Option.bind_some] at hq
              rw [Array.getElem?_set_self hi]
              simp only [Option.bind_some]
              have := ih slots[i] e' x y he' h2 h3 h4 q' z hq
              refine ⟨fun hn => this.1 (fun hp => hn (by simpa using hp)), fun hp => this.2 (by simpa using hp)⟩
            · rw [Array.getElem?_set]; simp only [hij, ite_false]
              exact ⟨fun _ => hq, fun hp => absurd (List.cons_prefix_cons.1 hp).1.symm hij⟩
        · simp at h1
      · simp at h1
    | _ => simp [Val.modifyAt?] at h1

theorem modifyAt_get_updated_subpath (f : Val → Option Val) :
    ∀ (p : List Nat) (v v' x y : Val) (q : List Nat) (z : Val),
      v.modifyAt? p f = some v' → v.get? p = some x → f x = some y →
      y.get? q = some z → v'.get? (p ++ q) = some z := by
  intro p
  induction p with
  | nil =>
    intro v v' x y q z hmodify hget hwrite hchild
    simp [Val.modifyAt?] at hmodify
    simp [Val.get?] at hget
    subst x
    rw [hwrite] at hmodify
    cases hmodify
    simpa using hchild
  | cons i rest ih =>
    intro v v' x y q z hmodify hget hwrite hchild
    cases v with
    | fixed es =>
      simp only [Val.modifyAt?] at hmodify
      split at hmodify
      · rename_i hi
        split at hmodify
        · rename_i e' he'
          cases hmodify
          rw [get_fixed, Array.getElem?_eq_getElem hi] at hget
          simp only [Option.bind_some] at hget
          rw [List.cons_append, get_fixed, Array.getElem?_set_self hi]
          simp only [Option.bind_some]
          exact ih es[i] e' x y q z he' hget hwrite hchild
        · simp at hmodify
      · simp at hmodify
    | record sid es =>
      simp only [Val.modifyAt?] at hmodify
      split at hmodify
      · rename_i hi
        split at hmodify
        · rename_i e' he'
          cases hmodify
          rw [get_record, Array.getElem?_eq_getElem hi] at hget
          simp only [Option.bind_some] at hget
          rw [List.cons_append, get_record, Array.getElem?_set_self hi]
          simp only [Option.bind_some]
          exact ih es[i] e' x y q z he' hget hwrite hchild
        · simp at hmodify
      · simp at hmodify
    | resizable E es =>
      simp only [Val.modifyAt?] at hmodify
      split at hmodify
      · rename_i hi
        split at hmodify
        · rename_i e' he'
          cases hmodify
          rw [get_resizable, Array.getElem?_eq_getElem hi] at hget
          simp only [Option.bind_some] at hget
          rw [List.cons_append, get_resizable, Array.getElem?_set_self hi]
          simp only [Option.bind_some]
          exact ih es[i] e' x y q z he' hget hwrite hchild
        · simp at hmodify
      · simp at hmodify
    | limited E capacity slots len =>
      simp only [Val.modifyAt?] at hmodify
      split at hmodify
      · rename_i hi
        split at hmodify
        · rename_i e' he'
          cases hmodify
          rw [get_limited, Array.getElem?_eq_getElem hi] at hget
          simp only [Option.bind_some] at hget
          rw [List.cons_append, get_limited, Array.getElem?_set_self hi]
          simp only [Option.bind_some]
          exact ih slots[i] e' x y q z he' hget hwrite hchild
        · simp at hmodify
      · simp at hmodify
    | _ => simp [Val.modifyAt?] at hmodify


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

theorem modify_except_root (s s' : Store) (o : Loc) (f : Val → Option Val)
    (h : s.modify o f = .ok s') :
    StoreLeExcept (fun r => r = o.root) s s' := by
  obtain ⟨old, x, y, new, ho, hx, hy, hmod, hroots⟩ := modify_spec s s' o f h
  intro r hr
  rw [hroots]
  simp [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Ne.symm hr]

/-! Resizable shrink keeps the owner and its ancestors, locations outside its
root, and descendants of elements below the new visible length. -/
def ResizableRetainedLoc (o : Loc) (len : Nat) (l : Loc) : Prop :=
  l.root ≠ o.root ∨ (l.root = o.root ∧ l.path <+: o.path) ∨
    (l.root = o.root ∧ ∃ i suffix, l.path = o.path ++ i :: suffix ∧ i < len)

/-! Limited shrink changes only visible length. Every previously written slot
and its descendants remain stored, so retention is bounded by the old
high-water extent rather than the new visible length. -/
def LimitedRetainedLoc (o : Loc) (slots : Array Val) (l : Loc) : Prop :=
  l.root ≠ o.root ∨ (l.root = o.root ∧ l.path <+: o.path) ∨
    (l.root = o.root ∧ ∃ i suffix, l.path = o.path ++ i :: suffix ∧ i < slots.size)

/- Existing soundness callers use `RetainedLoc` only for resizable truncation. -/
abbrev RetainedLoc := ResizableRetainedLoc

def LimitedRetainedSlice (o : Loc) (slots : Array Val) (l : Loc) (start count : Nat) : Prop :=
  LimitedRetainedLoc o slots l ∧
    (l.root ≠ o.root ∨ l.path ≠ o.path ∨ start + count ≤ slots.size)

theorem truncate_except_owner (s s' : Store) (o : Loc) (len : Nat)
    (h : s.truncate o len = .ok s') :
    StoreLeExcept (fun r => r = o.root) s s' := by
  exact modify_except_root s s' o (Val.truncate len) (by simpa [Store.truncate] using h)

theorem truncate_growshrink_shape (s s' : Store) (o : Loc) (len : Nat) (E : Ty)
    (hl : LocTy s o (.growshrink E)) (h : s.truncate o len = .ok s') :
    ∃ es, s.read o = .ok (.resizable E es) ∧ len ≤ es.size ∧
      s'.read o = .ok (.resizable E (es.extract 0 len)) ∧
      LocTy s' o (.growshrink E) := by
  have hm : s.modify o (Val.truncate len) = .ok s' := by simpa [Store.truncate] using h
  obtain ⟨old, x, y, new, ho, hx, hy, hmod, hroots⟩ :=
    modify_spec s s' o (Val.truncate len) hm
  obtain ⟨v, hread, hflat⟩ := hl
  obtain ⟨old1, ho1, hg1⟩ := (read_ok_iff _ _ _).1 hread
  rw [ho] at ho1; cases ho1
  rw [hx] at hg1
  have hxval : x = v := by cases hg1; rfl
  subst v
  cases x with
  | resizable E' es =>
    simp only [FlatTy] at hflat
    rcases hflat with ⟨rfl, helem⟩
    simp only [Val.truncate] at hy
    split at hy
    · rename_i hlen
      simp only [Option.some.injEq] at hy
      cases hy
      have hflat' : FlatTy (.growshrink E) (.resizable E (es.extract 0 len)) :=
        flat_resizable_extract (.growshrink E) E es len hlen ⟨rfl, helem⟩
      have hget := modifyAt_get_same (Val.truncate len) o.path old new
        (.resizable E es) (.resizable E (es.extract 0 len)) hmod hx
        (by simp [Val.truncate, hlen])
      have hpost : s'.read o = .ok (.resizable E (es.extract 0 len)) := by
        rw [read_ok_iff]
        exact ⟨new, by rw [hroots]; simp, hget⟩
      exact ⟨es, hread, hlen, hpost, ⟨_, hpost, hflat'⟩⟩
    · simp at hy
  | _ => simp [FlatTy] at hflat

theorem truncate_growshrink_preserves_retained (s s' : Store) (o : Loc) (len : Nat) (E : Ty)
    (hl : LocTy s o (.growshrink E)) (h : s.truncate o len = .ok s') :
    ∃ es, s.read o = .ok (.resizable E es) ∧ len ≤ es.size ∧
      ∀ (i : Nat) (q : List Nat) (z : Val), i < len →
        (Val.resizable E es).get? (i :: q) = some z →
        s'.read ⟨o.root, o.path ++ i :: q⟩ = .ok z := by
  obtain ⟨es, hread, hlen, hpost, _⟩ := truncate_growshrink_shape s s' o len E hl h
  refine ⟨es, hread, hlen, ?_⟩
  intro i q z hi hget
  have hchild : (Val.resizable E (es.extract 0 len)).get? (i :: q) = some z := by
    rw [get_resizable] at hget ⊢
    cases he : es[i]? with
    | none => simp [he] at hget
    | some e =>
      simp only [he, Option.bind_some] at hget
      have hidx : (es.extract 0 len)[i]? = some e := by
        rw [Array.getElem?_extract]
        split
        · simpa [Nat.zero_add] using he
        · omega
      rw [hidx]
      exact hget
  obtain ⟨newRoot, hroot, howner⟩ := (read_ok_iff _ _ _).1 hpost
  rw [read_ok_iff]
  refine ⟨newRoot, hroot, ?_⟩
  rw [get_append, howner]
  simp only [Option.bind_some]
  exact hchild

theorem truncate_growshrink_locTy (s s' : Store) (o l : Loc) (len : Nat) (E T : Ty)
    (hl : LocTy s o (.growshrink E)) (htruncate : s.truncate o len = .ok s')
    (hkeep : RetainedLoc o len l)
    (h : LocTy s l T) : LocTy s' l T := by
  rcases hkeep with hother | ⟨hroot, hprefix⟩ | ⟨hroot, i, q, hpath, hi⟩
  · obtain ⟨v, hread, hflat⟩ := h
    obtain ⟨old, hold, hget⟩ := (read_ok_iff _ _ _).1 hread
    exact ⟨v, (read_ok_iff _ _ _).2 ⟨old,
      by rw [truncate_except_owner s s' o len htruncate _ hother]; exact hold, hget⟩, hflat⟩
  · rcases hprefix with ⟨suffix, hsuffix⟩
    have hm : s.modify o (Val.truncate len) = .ok s' := by
      simpa [Store.truncate] using htruncate
    obtain ⟨oldRoot, x, y, newRoot, hrootOld, hx, hwrite, hmod, hroots⟩ :=
      modify_spec s s' o (Val.truncate len) hm
    obtain ⟨es, hownerRead, hlen, _, _⟩ := truncate_growshrink_shape s s' o len E hl htruncate
    obtain ⟨ownerRoot, hownerRoot, hownerGet⟩ := (read_ok_iff _ _ _).1 hownerRead
    rw [hrootOld] at hownerRoot
    cases hownerRoot
    have hxOwner : x = .resizable E es := by
      rw [hownerGet] at hx
      exact (Option.some.inj hx).symm
    subst x
    have hwrite' : y = .resizable E (es.extract 0 len) := by
      simpa [Val.truncate, hlen] using hwrite.symm
    subst y
    obtain ⟨v, hread, hflat⟩ := h
    obtain ⟨oldAtLoc, hlocRoot, hlocGet⟩ := (read_ok_iff _ _ _).1 hread
    rw [hroot] at hlocRoot
    rw [hrootOld] at hlocRoot
    cases hlocRoot
    obtain ⟨oldLoc, newLoc, holdLoc, hnewLoc, hmodLoc⟩ :=
      modifyAt_prefix_decompose (Val.truncate len) l.path suffix oldRoot newRoot
        (by rw [hsuffix]; exact hmod)
    have hlocEq : oldLoc = v := by rw [hlocGet] at holdLoc; exact (Option.some.inj holdLoc).symm
    subst oldLoc
    have hownerAtLoc : v.get? suffix = some (.resizable E es) := by
      have hx' := hx
      rw [← hsuffix, get_append, hlocGet] at hx'
      exact hx'
    have htypes : ∀ U, FlatTy U (.resizable E es) →
        FlatTy U (.resizable E (es.extract 0 len)) := by
      intro U hU
      exact flat_resizable_extract U E es len hlen hU
    have hflat' : FlatTy T newLoc :=
      flat_modifyAt_type (Val.truncate len) suffix v newLoc (.resizable E es)
        (.resizable E (es.extract 0 len)) hmodLoc hownerAtLoc
        (by simp [Val.truncate, hlen]) htypes T hflat
    have hread' : s'.read l = .ok newLoc := by
      rw [read_ok_iff]
      exact ⟨newRoot, by rw [hroot, hroots]; simp, hnewLoc⟩
    exact ⟨newLoc, hread', hflat'⟩
  · have heq : l = ⟨o.root, o.path ++ i :: q⟩ := by
      cases l
      cases o
      simp_all
    subst l
    obtain ⟨es, howner, hlen, hretained⟩ :=
      truncate_growshrink_preserves_retained s s' o len E hl htruncate
    obtain ⟨v, hread, hflat⟩ := h
    obtain ⟨old, hold, hget⟩ := (read_ok_iff _ _ _).1 hread
    obtain ⟨ownerRoot, hownerRoot, hownerGet⟩ := (read_ok_iff _ _ _).1 howner
    have hrootEq : ownerRoot = old := by rw [hownerRoot] at hold; cases hold; rfl
    subst old
    have hsub : (Val.resizable E es).get? (i :: q) = some v := by
      rw [get_append, hownerGet] at hget
      simpa using hget
    exact ⟨v, hretained i q v hi hsub, hflat⟩

theorem LocTy.grow_to_growshrink {s : Store} {l : Loc} {E : Ty}
    (h : LocTy s l (.grow E)) : LocTy s l (.growshrink E) := by
  obtain ⟨v, hread, hflat⟩ := h
  cases v with
  | resizable E' es =>
    simp only [FlatTy] at hflat ⊢
    rcases hflat with ⟨hE, hitems⟩
    subst E'
    exact ⟨Val.resizable E es, hread, ⟨rfl, hitems⟩⟩
  | _ => simp [FlatTy] at hflat

theorem LocTy.growshrink_to_grow {s : Store} {l : Loc} {E : Ty}
    (h : LocTy s l (.growshrink E)) : LocTy s l (.grow E) := by
  obtain ⟨v, hread, hflat⟩ := h
  cases v with
  | resizable E' es =>
    simp only [FlatTy] at hflat ⊢
    rcases hflat with ⟨hE, hitems⟩
    subst E'
    exact ⟨Val.resizable E es, hread, ⟨rfl, hitems⟩⟩
  | _ => simp [FlatTy] at hflat

/-- `grow` and `growshrink` share the same resizable representation. A valid
shrink therefore preserves either owner type at its header. -/
theorem truncate_grow_shape (s s' : Store) (o : Loc) (len : Nat) (E : Ty)
    (hl : LocTy s o (.grow E)) (h : s.truncate o len = .ok s') :
    ∃ es, s.read o = .ok (.resizable E es) ∧ len ≤ es.size ∧
      s'.read o = .ok (.resizable E (es.extract 0 len)) ∧
      LocTy s' o (.grow E) := by
  obtain ⟨es, hread, hlen, hpost, hloc⟩ :=
    truncate_growshrink_shape s s' o len E hl.grow_to_growshrink h
  refine ⟨es, hread, hlen, hpost, ?_⟩
  exact hloc.growshrink_to_grow

/-- Retained paths into a shrinking `grow` owner remain typed. -/
theorem truncate_grow_locTy (s s' : Store) (o l : Loc) (len : Nat) (E T : Ty)
    (hl : LocTy s o (.grow E)) (htruncate : s.truncate o len = .ok s')
    (hkeep : RetainedLoc o len l) (h : LocTy s l T) : LocTy s' l T := by
  exact truncate_growshrink_locTy s s' o l len E T hl.grow_to_growshrink
    htruncate hkeep h

theorem truncate_limited_shape (s s' : Store) (o : Loc) (len : Nat)
    (E : Ty) (capacity : Nat) (hl : LocTy s o (.limited E capacity))
    (h : s.truncate o len = .ok s') :
    ∃ slots old, s.read o = .ok (.limited E capacity slots old) ∧ len ≤ old ∧
      s'.read o = .ok (.limited E capacity slots len) ∧
      LocTy s' o (.limited E capacity) := by
  have hm : s.modify o (Val.truncate len) = .ok s' := by
    simpa [Store.truncate] using h
  obtain ⟨root, x, y, new, hroot, hget, hnew, hmod, hroots⟩ :=
    modify_spec s s' o (Val.truncate len) hm
  obtain ⟨v, hread, hflat⟩ := hl
  obtain ⟨oldRoot, hrootRead, hownerGet⟩ := (read_ok_iff _ _ _).1 hread
  rw [hroot] at hrootRead
  cases hrootRead
  have hx : x = v := by
    rw [hget] at hownerGet
    cases hownerGet
    rfl
  subst v
  cases x with
  | limited E' capacity' slots old =>
    simp only [FlatTy] at hflat
    rcases hflat with ⟨rfl, rfl, hcap, hsize, hslots⟩
    simp only [Val.truncate] at hnew
    split at hnew
    · rename_i hlen
      simp only [Option.some.injEq] at hnew
      cases hnew
      have hflat' : FlatTy (.limited E capacity) (.limited E capacity slots len) :=
        flat_limited_truncate (.limited E capacity) E capacity slots old len hlen
          ⟨rfl, rfl, hcap, hsize, hslots⟩
      have hgetOwner := modifyAt_get_same (Val.truncate len) o.path root new
        (.limited E capacity slots old) (.limited E capacity slots len) hmod hget
        (by simp [Val.truncate, hlen])
      have hpost : s'.read o = .ok (.limited E capacity slots len) := by
        rw [read_ok_iff]
        exact ⟨new, by rw [hroots]; simp, hgetOwner⟩
      exact ⟨slots, old, hread, hlen, hpost, ⟨_, hpost, hflat'⟩⟩
    · simp at hnew
  | _ => simp [FlatTy] at hflat

theorem truncate_limited_le (s s' : Store) (o : Loc) (len : Nat)
    (E : Ty) (capacity : Nat) (hl : LocTy s o (.limited E capacity))
    (h : s.truncate o len = .ok s') :
    StoreLe s s' ∧ LocTy s' o (.limited E capacity) ∧
      ∃ slots old, s.read o = .ok (.limited E capacity slots old) ∧ len ≤ old ∧
        s'.read o = .ok (.limited E capacity slots len) := by
  obtain ⟨slots, old, hread, hlen, hpost, hloc⟩ :=
    truncate_limited_shape s s' o len E capacity hl h
  have hm : s.modify o (Val.truncate len) = .ok s' := by
    simpa [Store.truncate] using h
  have hle : StoreLe s s' := by
    apply modify_le s s' o (Val.truncate len) hm
    intro root x y hroot hget hnew
    obtain ⟨oldRoot, hrootRead, hownerGet⟩ := (read_ok_iff _ _ _).1 hread
    rw [hroot] at hrootRead
    cases hrootRead
    have hx : x = .limited E capacity slots old := by
      rw [hget] at hownerGet
      cases hownerGet
      rfl
    subst x
    simp only [Val.truncate] at hnew
    rw [if_pos hlen] at hnew
    simp only [Option.some.injEq] at hnew
    cases hnew
    exact refines_limitedTruncate E capacity slots old len hlen
  exact ⟨hle, hloc, slots, old, hread, hlen, hpost⟩

theorem truncate_limited_preserves_written (s s' : Store) (o : Loc) (len : Nat)
    (E : Ty) (capacity : Nat) (hl : LocTy s o (.limited E capacity))
    (h : s.truncate o len = .ok s') :
    ∃ slots old, s.read o = .ok (.limited E capacity slots old) ∧ len ≤ old ∧
      ∀ (i : Nat) (q : List Nat) (z : Val),
        (Val.limited E capacity slots old).get? (i :: q) = some z →
        s'.read ⟨o.root, o.path ++ i :: q⟩ = .ok z := by
  obtain ⟨slots, old, hread, hlen, hpost, _⟩ :=
    truncate_limited_shape s s' o len E capacity hl h
  refine ⟨slots, old, hread, hlen, ?_⟩
  intro i q z hget
  have hchild : (Val.limited E capacity slots len).get? (i :: q) = some z := by
    rw [get_limited] at hget ⊢
    exact hget
  obtain ⟨newRoot, hroot, howner⟩ := (read_ok_iff _ _ _).1 hpost
  rw [read_ok_iff]
  refine ⟨newRoot, hroot, ?_⟩
  rw [get_append, howner]
  simp only [Option.bind_some]
  exact hchild

theorem truncate_limited_locTy_written (s s' : Store) (o l : Loc) (len : Nat)
    (E : Ty) (capacity : Nat) (T : Ty)
    (slots : Array Val) (howner : ∃ old, s.read o = .ok (.limited E capacity slots old))
    (hl : LocTy s o (.limited E capacity))
    (htruncate : s.truncate o len = .ok s')
    (hkeep : LimitedRetainedLoc o slots l) (h : LocTy s l T) : LocTy s' l T := by
  rcases hkeep with hother | ⟨hroot, hprefix⟩ | ⟨hroot, i, q, hpath, hi⟩
  · obtain ⟨v, hread, hflat⟩ := h
    obtain ⟨old, hold, hget⟩ := (read_ok_iff _ _ _).1 hread
    exact ⟨v, (read_ok_iff _ _ _).2 ⟨old,
      by rw [truncate_except_owner s s' o len htruncate _ hother]; exact hold, hget⟩, hflat⟩
  · rcases hprefix with ⟨suffix, hsuffix⟩
    have hm : s.modify o (Val.truncate len) = .ok s' := by
      simpa [Store.truncate] using htruncate
    obtain ⟨oldRoot, x, y, newRoot, hrootOld, hx, hwrite, hmod, hroots⟩ :=
      modify_spec s s' o (Val.truncate len) hm
    obtain ⟨slots', oldLen, hownerRead, hlen, _, _⟩ :=
      truncate_limited_shape s s' o len E capacity hl htruncate
    have hslots : slots' = slots := by
      obtain ⟨ownerOld, hownerRead'⟩ := howner
      rw [hownerRead] at hownerRead'
      cases hownerRead'
      rfl
    obtain ⟨ownerRoot, hownerRoot, hownerGet⟩ := (read_ok_iff _ _ _).1 hownerRead
    rw [hrootOld] at hownerRoot
    cases hownerRoot
    have hxOwner : x = .limited E capacity slots' oldLen := by
      rw [hownerGet] at hx
      exact (Option.some.inj hx).symm
    subst x
    have hwrite' : y = .limited E capacity slots' len := by
      simpa [Val.truncate, hlen] using hwrite.symm
    subst y
    obtain ⟨v, hread, hflat⟩ := h
    obtain ⟨oldAtLoc, hlocRoot, hlocGet⟩ := (read_ok_iff _ _ _).1 hread
    rw [hroot] at hlocRoot
    rw [hrootOld] at hlocRoot
    cases hlocRoot
    obtain ⟨oldLoc, newLoc, holdLoc, hnewLoc, hmodLoc⟩ :=
      modifyAt_prefix_decompose (Val.truncate len) l.path suffix oldRoot newRoot
        (by rw [hsuffix]; exact hmod)
    have hlocEq : oldLoc = v := by rw [hlocGet] at holdLoc; exact (Option.some.inj holdLoc).symm
    subst oldLoc
    have hownerAtLoc : v.get? suffix = some (.limited E capacity slots' oldLen) := by
      have hx' := hx
      rw [← hsuffix, get_append, hlocGet] at hx'
      exact hx'
    have htypes : ∀ U, FlatTy U (.limited E capacity slots' oldLen) →
        FlatTy U (.limited E capacity slots' len) := by
      intro U hU
      exact flat_limited_truncate U E capacity slots' oldLen len hlen hU
    have hflat' : FlatTy T newLoc :=
      flat_modifyAt_type (Val.truncate len) suffix v newLoc
        (.limited E capacity slots' oldLen) (.limited E capacity slots' len)
        hmodLoc hownerAtLoc (by simp [Val.truncate, hlen]) htypes T hflat
    have hread' : s'.read l = .ok newLoc := by
      rw [read_ok_iff]
      exact ⟨newRoot, by rw [hroot, hroots]; simp, hnewLoc⟩
    exact ⟨newLoc, hread', hflat'⟩
  · have heq : l = ⟨o.root, o.path ++ i :: q⟩ := by
      cases l
      cases o
      simp_all
    subst l
    obtain ⟨slots', oldLen, hownerRead, hlen, hretained⟩ :=
      truncate_limited_preserves_written s s' o len E capacity hl htruncate
    have hslots : slots' = slots := by
      obtain ⟨ownerOld, hownerRead'⟩ := howner
      rw [hownerRead] at hownerRead'
      cases hownerRead'
      rfl
    obtain ⟨v, hread, hflat⟩ := h
    obtain ⟨old, hold, hget⟩ := (read_ok_iff _ _ _).1 hread
    obtain ⟨ownerRoot, hownerRoot, hownerGet⟩ := (read_ok_iff _ _ _).1 hownerRead
    have hrootEq : ownerRoot = old := by rw [hownerRoot] at hold; cases hold; rfl
    subst old
    have hsub : (Val.limited E capacity slots' oldLen).get? (i :: q) = some v := by
      rw [get_append, hownerGet] at hget
      simpa using hget
    have hread' := hretained i q v hsub
    exact ⟨v, by simpa [hslots] using hread', hflat⟩

theorem truncate_limited_locTy (s s' : Store) (o l : Loc) (len : Nat)
    (E : Ty) (capacity : Nat) (T : Ty)
    (hl : LocTy s o (.limited E capacity))
    (htruncate : s.truncate o len = .ok s')
    (hkeep : RetainedLoc o len l) (h : LocTy s l T) : LocTy s' l T := by
  obtain ⟨slots, oldLen, hownerRead, hlen, _, _⟩ :=
    truncate_limited_shape s s' o len E capacity hl htruncate
  have hhigh : oldLen ≤ slots.size := by
    obtain ⟨v, hread, hflat⟩ := hl
    rw [hownerRead] at hread
    cases hread
    simpa only [FlatTy] using hflat.2.2.2.1
  apply truncate_limited_locTy_written s s' o l len E capacity T slots ⟨oldLen, hownerRead⟩
    hl htruncate ?_ h
  rcases hkeep with hother | hprefix | ⟨hroot, i, suffix, hpath, hi⟩
  · exact Or.inl hother
  · exact Or.inr (Or.inl hprefix)
  · exact Or.inr (Or.inr ⟨hroot, i, suffix, hpath, by omega⟩)

/-- A successful resizable truncation returns the exact new header and leaves
every other root unchanged. This is the common store contract for pop, popN,
shrinking resize, and clear. -/
theorem truncate_growshrink_step (s s' : Store) (o : Loc) (len : Nat) (E : Ty)
    (hl : LocTy s o (.growshrink E)) (htruncate : s.truncate o len = .ok s') :
    StoreLeExcept (fun r => r = o.root) s s' ∧
      ∃ es, s.read o = .ok (.resizable E es) ∧ len ≤ es.size ∧
        s'.read o = .ok (.resizable E (es.extract 0 len)) ∧
        LocTy s' o (.growshrink E) := by
  exact ⟨truncate_except_owner s s' o len htruncate,
    truncate_growshrink_shape s s' o len E hl htruncate⟩

/-- The corresponding contract for a `grow` owner. Its written suffix is
released just like the suffix of a `growshrink` owner. -/
theorem truncate_grow_step (s s' : Store) (o : Loc) (len : Nat) (E : Ty)
    (hl : LocTy s o (.grow E)) (htruncate : s.truncate o len = .ok s') :
    StoreLeExcept (fun r => r = o.root) s s' ∧
      ∃ es, s.read o = .ok (.resizable E es) ∧ len ≤ es.size ∧
        s'.read o = .ok (.resizable E (es.extract 0 len)) ∧
        LocTy s' o (.grow E) := by
  exact ⟨truncate_except_owner s s' o len htruncate,
    truncate_grow_shape s s' o len E hl htruncate⟩

/-- A successful limited truncation keeps the backing extent and every read in
previously written slots. The visible length may be smaller than those slots. -/
theorem truncate_limited_step (s s' : Store) (o : Loc) (len : Nat)
    (E : Ty) (capacity : Nat) (hl : LocTy s o (.limited E capacity))
    (htruncate : s.truncate o len = .ok s') :
    StoreLeExcept (fun r => r = o.root) s s' ∧
      ∃ slots old, s.read o = .ok (.limited E capacity slots old) ∧
        len ≤ old ∧ old ≤ slots.size ∧
        (∀ (i : Nat) (e : Val), slots[i]? = some e → FlatTy E e) ∧
        s'.read o = .ok (.limited E capacity slots len) ∧
        LocTy s' o (.limited E capacity) ∧
        (∀ (i : Nat) (q : List Nat) (z : Val),
          (Val.limited E capacity slots old).get? (i :: q) = some z →
          s'.read ⟨o.root, o.path ++ i :: q⟩ = .ok z) := by
  obtain ⟨slots, old, hread, hlen, hpost, hloc⟩ :=
    truncate_limited_shape s s' o len E capacity hl htruncate
  obtain ⟨slots', old', hread', hlen', hwritten⟩ :=
    truncate_limited_preserves_written s s' o len E capacity hl htruncate
  have hsame : Val.limited E capacity slots old = Val.limited E capacity slots' old' :=
    Except.ok.inj (hread.symm.trans hread')
  cases hsame
  obtain ⟨v, hv, hflat⟩ := hl
  rw [hread] at hv
  cases hv
  simp only [FlatTy] at hflat
  rcases hflat with ⟨_, ⟨_, hcap, hhigh, hslots⟩⟩
  exact ⟨truncate_except_owner s s' o len htruncate,
    ⟨slots, old, hread, hlen, hhigh, hslots, hpost, hloc, hwritten⟩⟩

/-- `pop` snapshots its last element before truncating the owner. The returned
element is flat even though its original location is removed by the shrink. -/
theorem pop_snapshot_growshrink (s s' : Store) (o : Loc) (len : Nat) (E : Ty) (v : Val)
    (hl : LocTy s o (.growshrink E))
    (hlen : s.length o = .ok (len + 1))
    (hread : s.read ⟨o.root, o.path ++ [len]⟩ = .ok v)
    (htruncate : s.truncate o len = .ok s') :
    ∃ es, s.read o = .ok (.resizable E es) ∧ es.size = len + 1 ∧
      FlatTy E v ∧ s'.read o = .ok (.resizable E (es.extract 0 len)) := by
  rcases length_ok s o (len + 1) hlen with hresizable | hlimited
  · obtain ⟨E', es, howner, hsize⟩ := hresizable
    have htype : E' = E := by
      obtain ⟨old, hold, hflat⟩ := hl
      rw [howner] at hold
      cases hold
      simpa only [FlatTy] using hflat.1.symm
    cases htype
    have hslot := (read_resizableElem_iff howner).1 hread
    have hitems : ∀ (i : Nat) (e : Val), es[i]? = some e → FlatTy E e := by
      obtain ⟨old, hold, hflat⟩ := hl
      rw [howner] at hold
      cases hold
      simpa only [FlatTy] using hflat.2
    have hvalue := hitems len v hslot
    obtain ⟨es', howner', _, hpost, _⟩ :=
      truncate_growshrink_shape s s' o len E hl htruncate
    have hsame : Val.resizable E es = Val.resizable E es' :=
      Except.ok.inj (howner.symm.trans howner')
    have harrays : es = es' := by injection hsame
    subst es'
    exact ⟨es, howner, hsize.symm, hvalue, hpost⟩
  · obtain ⟨E', capacity, slots, old, howner, _⟩ := hlimited
    obtain ⟨owner, hreadOwner, hflat⟩ := hl
    rw [howner] at hreadOwner
    cases hreadOwner
    simp only [FlatTy] at hflat

/-- For a limited owner, the same pre-truncate snapshot remains readable in the
backing slot after the visible length decreases. -/
theorem pop_snapshot_limited (s s' : Store) (o : Loc) (len : Nat)
    (E : Ty) (capacity : Nat) (v : Val)
    (hl : LocTy s o (.limited E capacity))
    (hlen : s.length o = .ok (len + 1))
    (hread : s.read ⟨o.root, o.path ++ [len]⟩ = .ok v)
    (htruncate : s.truncate o len = .ok s') :
    ∃ slots, s.read o = .ok (.limited E capacity slots (len + 1)) ∧
      len < slots.size ∧ FlatTy E v ∧
      s'.read ⟨o.root, o.path ++ [len]⟩ = .ok v ∧
      s'.read o = .ok (.limited E capacity slots len) := by
  have hlimited : LocTy s o (.limited E capacity) := hl
  obtain ⟨old, howner, hflat⟩ := hl
  cases old with
  | limited E' capacity' slots oldLen =>
    have hlen' : oldLen = len + 1 := by
      simpa [Store.length, howner] using hlen
    have hElem : E' = E := by
      simp only [FlatTy] at hflat
      exact hflat.1.symm
    have hCapacity : capacity' = capacity := by
      simp only [FlatTy] at hflat
      exact hflat.2.1.symm
    subst E'
    subst capacity'
    subst oldLen
    have hslot := (read_limitedElem_iff howner).1 hread
    have hitems : ∀ (i : Nat) (e : Val), slots[i]? = some e → FlatTy E e := by
      simpa only [FlatTy] using hflat.2.2.2.2
    have hvalue := hitems len v hslot
    obtain ⟨_, ⟨slots', old', howner', hlenRetained, hcapacityBound, hslotsTyped,
        hpost, hpostTyped, hwritten⟩⟩ :=
      truncate_limited_step s s' o len E capacity hlimited htruncate
    have hsame : Val.limited E capacity slots (len + 1) =
        Val.limited E capacity slots' old' :=
      Except.ok.inj (howner.symm.trans howner')
    cases hsame
    have hpostSlot := hwritten len [] v (by simpa [get_limited, hslot, get_nil])
    exact ⟨slots, howner, by omega, hvalue, hpostSlot, hpost⟩
  | _ => simp [FlatTy] at hflat

private theorem replicated_elements_flat {E : Ty} {fill : Val} {count : Nat}
    (hfill : FlatTy E fill) :
    ∀ (i : Nat) (e : Val), (Array.replicate count fill)[i]? = some e → FlatTy E e := by
  intro i e he
  rw [Array.getElem?_replicate] at he
  split at he <;> simp_all

/-- The growth branch of `resize` appends a repeated, already evaluated fill
value. The length premise is sampled after the size and fill expressions run. -/
theorem resize_grow_grow (s s' : Store) (o : Loc) (oldSize newSize : Nat)
    (E : Ty) (fill : Val) (hl : LocTy s o (.grow E))
    (hfill : FlatTy E fill) (hlen : s.length o = .ok oldSize)
    (hgrows : oldSize < newSize)
    (happend : s.append o (Array.replicate (newSize - oldSize) fill) = .ok (s', oldSize)) :
    StoreLe s s' ∧ LocTy s' o (.grow E) ∧
      s.length o = .ok oldSize ∧ oldSize < newSize ∧
      ∃ es, s.read o = .ok (.resizable E es) ∧ es.size = oldSize ∧
        (∀ i, i < newSize - oldSize →
          s'.read ⟨o.root, o.path ++ [oldSize + i]⟩ = .ok fill) := by
  have hvs := replicated_elements_flat (count := newSize - oldSize) hfill
  obtain ⟨hle, hloc, es, hread, hsize, happended⟩ :=
    append_le s s' o (Array.replicate (newSize - oldSize) fill) oldSize E hl hvs happend
  have hsize' : es.size = oldSize := hsize.symm
  refine ⟨hle, hloc, hlen, hgrows, es, hread, hsize', ?_⟩
  intro i hi
  apply happended i fill
  simp [hi]

/-- The `growshrink` form of the resize growth branch. -/
theorem resize_grow_growshrink (s s' : Store) (o : Loc) (oldSize newSize : Nat)
    (E : Ty) (fill : Val) (hl : LocTy s o (.growshrink E))
    (hfill : FlatTy E fill) (hlen : s.length o = .ok oldSize)
    (hgrows : oldSize < newSize)
    (happend : s.append o (Array.replicate (newSize - oldSize) fill) = .ok (s', oldSize)) :
    StoreLe s s' ∧ LocTy s' o (.growshrink E) ∧
      s.length o = .ok oldSize ∧ oldSize < newSize ∧
      ∃ es, s.read o = .ok (.resizable E es) ∧ es.size = oldSize ∧
        (∀ i, i < newSize - oldSize →
          s'.read ⟨o.root, o.path ++ [oldSize + i]⟩ = .ok fill) := by
  have hvs := replicated_elements_flat (count := newSize - oldSize) hfill
  obtain ⟨hle, hloc, es, hread, hsize, happended⟩ :=
    append_le_growshrink s s' o (Array.replicate (newSize - oldSize) fill)
      oldSize E hl hvs happend
  have hsize' : es.size = oldSize := hsize.symm
  refine ⟨hle, hloc, hlen, hgrows, es, hread, hsize', ?_⟩
  intro i hi
  apply happended i fill
  simp [hi]

/-- Limited resize growth writes the evaluated fill into new visible slots,
preserves the old visible prefix, and checks the requested length against the
owner capacity before appending. -/
theorem resize_grow_limited (s s' : Store) (o : Loc) (oldSize newSize : Nat)
    (E : Ty) (capacity : Nat) (fill : Val) (hE : E.flat = true)
    (hl : LocTy s o (.limited E capacity)) (hfill : FlatTy E fill)
    (hlen : s.length o = .ok oldSize) (hgrows : oldSize < newSize)
    (hcapacity : newSize ≤ capacity)
    (happend : s.append o (Array.replicate (newSize - oldSize) fill) = .ok (s', oldSize)) :
    StoreLe s s' ∧ LocTy s' o (.limited E capacity) ∧
      s.length o = .ok oldSize ∧ oldSize < newSize ∧ newSize ≤ capacity ∧
      ∃ slots, s.read o = .ok (.limited E capacity slots oldSize) ∧
        oldSize ≤ slots.size ∧
        (∀ i, i < newSize - oldSize →
          s'.read ⟨o.root, o.path ++ [oldSize + i]⟩ = .ok fill) ∧
        (∀ i e, i < oldSize → slots[i]? = some e →
          s'.read ⟨o.root, o.path ++ [i]⟩ = .ok e) := by
  have hvs := replicated_elements_flat (count := newSize - oldSize) hfill
  obtain ⟨hle, hloc, slots, oldLen, hread, _, hslots, _,
      happended, hvisible⟩ :=
    append_le_limited s s' o (Array.replicate (newSize - oldSize) fill)
      oldSize E capacity hE hl hvs happend
  have hlenEq : oldLen = oldSize := by
    simpa [Store.length, hread] using hlen
  subst oldLen
  refine ⟨hle, hloc, hlen, hgrows, hcapacity, slots, hread, hslots, ?_, ?_⟩
  · intro i hi
    have he : (Array.replicate (newSize - oldSize) fill)[i]? = some fill := by
      simp [hi]
    have hreadFill := happended i fill he
    exact hreadFill
  · intro i e hi he
    exact hvisible i e hi he

/-- Clearing a resizable owner truncates it to an empty header and leaves
unrelated roots unchanged. -/
theorem clear_growshrink (s s' : Store) (o : Loc) (E : Ty)
    (hl : LocTy s o (.growshrink E)) (hclear : s.truncate o 0 = .ok s') :
    StoreLeExcept (fun r => r = o.root) s s' ∧
      ∃ es, s.read o = .ok (.resizable E es) ∧
        s'.read o = .ok (.resizable E #[]) ∧ LocTy s' o (.growshrink E) := by
  obtain ⟨hExcept, es, hread, _, hpost, hloc⟩ :=
    truncate_growshrink_step s s' o 0 E hl hclear
  have hempty : s'.read o = .ok (.resizable E #[]) := by simpa using hpost
  exact ⟨hExcept, es, hread, hempty, hloc⟩

/-- Limited clear sets visible length to zero but keeps every written backing
slot readable for aliases that still point into the old run. -/
theorem clear_limited (s s' : Store) (o : Loc) (E : Ty) (capacity : Nat)
    (hl : LocTy s o (.limited E capacity)) (hclear : s.truncate o 0 = .ok s') :
    StoreLeExcept (fun r => r = o.root) s s' ∧
      ∃ slots old, s.read o = .ok (.limited E capacity slots old) ∧
        old ≤ slots.size ∧
        (∀ (i : Nat) (e : Val), slots[i]? = some e → FlatTy E e) ∧
        s'.read o = .ok (.limited E capacity slots 0) ∧
        LocTy s' o (.limited E capacity) ∧
        (∀ (i : Nat) (q : List Nat) (z : Val),
          (Val.limited E capacity slots old).get? (i :: q) = some z →
          s'.read ⟨o.root, o.path ++ i :: q⟩ = .ok z) := by
  obtain ⟨hExcept, ⟨slots, old, hread, _, hhigh, hslots, hpost, hloc, hwritten⟩⟩ :=
    truncate_limited_step s s' o 0 E capacity hl hclear
  exact ⟨hExcept, slots, old, hread, hhigh, hslots, hpost, hloc, hwritten⟩

/-- The `.grow` owner form of clear. -/
theorem clear_grow (s s' : Store) (o : Loc) (E : Ty)
    (hl : LocTy s o (.grow E)) (hclear : s.truncate o 0 = .ok s') :
    StoreLeExcept (fun r => r = o.root) s s' ∧
      ∃ es, s.read o = .ok (.resizable E es) ∧
        s'.read o = .ok (.resizable E #[]) ∧ LocTy s' o (.grow E) := by
  obtain ⟨hExcept, es, hread, hempty, hloc⟩ :=
    clear_growshrink s s' o E hl.grow_to_growshrink hclear
  exact ⟨hExcept, es, hread, hempty, hloc.growshrink_to_grow⟩

/-- The `popN` range check guarantees that the evaluator's subtraction is
well-defined. This exposes its exact truncate target for resizable owners. -/
theorem popN_growshrink (s s' : Store) (o : Loc) (oldSize : Nat) (count : Int)
    (E : Ty) (hl : LocTy s o (.growshrink E))
    (hlen : s.length o = .ok oldSize) (hcountNonnegative : 0 ≤ count)
    (hcountBound : count ≤ (oldSize : Int))
    (htruncate : s.truncate o (oldSize - count.toNat) = .ok s') :
    StoreLeExcept (fun r => r = o.root) s s' ∧
      s.length o = .ok oldSize ∧ 0 ≤ count ∧ count ≤ (oldSize : Int) ∧
      ∃ es, s.read o = .ok (.resizable E es) ∧
        oldSize - count.toNat ≤ es.size ∧
        s'.read o = .ok (.resizable E (es.extract 0 (oldSize - count.toNat))) ∧
        LocTy s' o (.growshrink E) := by
  obtain ⟨hExcept, es, hread, hsize, hpost, hloc⟩ :=
    truncate_growshrink_step s s' o (oldSize - count.toNat) E hl htruncate
  exact ⟨hExcept, hlen, hcountNonnegative, hcountBound,
    es, hread, hsize, hpost, hloc⟩

/-- Limited `popN` keeps every old written slot through the same visible-length
decrease, including slots beyond the new length. -/
theorem popN_limited (s s' : Store) (o : Loc) (oldSize : Nat) (count : Int)
    (E : Ty) (capacity : Nat) (hl : LocTy s o (.limited E capacity))
    (hlen : s.length o = .ok oldSize) (hcountNonnegative : 0 ≤ count)
    (hcountBound : count ≤ (oldSize : Int))
    (htruncate : s.truncate o (oldSize - count.toNat) = .ok s') :
    StoreLeExcept (fun r => r = o.root) s s' ∧
      s.length o = .ok oldSize ∧ 0 ≤ count ∧ count ≤ (oldSize : Int) ∧
      ∃ slots old, s.read o = .ok (.limited E capacity slots old) ∧
        oldSize - count.toNat ≤ old ∧ old ≤ slots.size ∧
        (∀ (i : Nat) (e : Val), slots[i]? = some e → FlatTy E e) ∧
        s'.read o = .ok (.limited E capacity slots (oldSize - count.toNat)) ∧
        LocTy s' o (.limited E capacity) ∧
        (∀ (i : Nat) (q : List Nat) (z : Val),
          (Val.limited E capacity slots old).get? (i :: q) = some z →
          s'.read ⟨o.root, o.path ++ i :: q⟩ = .ok z) := by
  obtain ⟨hExcept, contract⟩ :=
    truncate_limited_step s s' o (oldSize - count.toNat) E capacity hl htruncate
  rcases contract with ⟨slots, old, hread, hlenRetained, hhigh, hslots, hpost, hloc, hwritten⟩
  exact ⟨hExcept, hlen, hcountNonnegative, hcountBound,
    slots, old, hread, hlenRetained, hhigh, hslots, hpost, hloc, hwritten⟩

/-- Shrinking `resize` is exactly the store truncation branch; any fill operand
has already been evaluated in the input store. -/
theorem resize_shrink_growshrink (s s' : Store) (o : Loc) (oldSize newSize : Nat)
    (E : Ty) (hl : LocTy s o (.growshrink E))
    (hlen : s.length o = .ok oldSize) (hshrinks : newSize < oldSize)
    (htruncate : s.truncate o newSize = .ok s') :
    StoreLeExcept (fun r => r = o.root) s s' ∧
      s.length o = .ok oldSize ∧ newSize < oldSize ∧
      ∃ es, s.read o = .ok (.resizable E es) ∧ newSize ≤ es.size ∧
        s'.read o = .ok (.resizable E (es.extract 0 newSize)) ∧
        LocTy s' o (.growshrink E) := by
  obtain ⟨hExcept, es, hread, hsize, hpost, hloc⟩ :=
    truncate_growshrink_step s s' o newSize E hl htruncate
  exact ⟨hExcept, hlen, hshrinks, es, hread, hsize, hpost, hloc⟩

/-- Limited shrinking `resize` keeps the entire written backing extent while
setting only its visible length to the requested size. -/
theorem resize_shrink_limited (s s' : Store) (o : Loc) (oldSize newSize : Nat)
    (E : Ty) (capacity : Nat) (hl : LocTy s o (.limited E capacity))
    (hlen : s.length o = .ok oldSize) (hshrinks : newSize < oldSize)
    (htruncate : s.truncate o newSize = .ok s') :
    StoreLeExcept (fun r => r = o.root) s s' ∧
      s.length o = .ok oldSize ∧ newSize < oldSize ∧
      ∃ slots old, s.read o = .ok (.limited E capacity slots old) ∧
        newSize ≤ old ∧ old ≤ slots.size ∧
        (∀ (i : Nat) (e : Val), slots[i]? = some e → FlatTy E e) ∧
        s'.read o = .ok (.limited E capacity slots newSize) ∧
        LocTy s' o (.limited E capacity) ∧
        (∀ (i : Nat) (q : List Nat) (z : Val),
          (Val.limited E capacity slots old).get? (i :: q) = some z →
          s'.read ⟨o.root, o.path ++ i :: q⟩ = .ok z) := by
  obtain ⟨hExcept, contract⟩ :=
    truncate_limited_step s s' o newSize E capacity hl htruncate
  rcases contract with ⟨slots, old, hread, hlenRetained, hhigh, hslots, hpost, hloc, hwritten⟩
  exact ⟨hExcept, hlen, hshrinks,
    slots, old, hread, hlenRetained, hhigh, hslots, hpost, hloc, hwritten⟩

/-- `assignWhole` truncates the old owner before evaluating the replacement.
This contract exposes the empty owner at that boundary, then accounts for the
replacement write after its expression has run. -/
theorem assignWhole_grow (s sClear sEval s' : Store) (o : Loc) (E : Ty)
    (es : Array Val) (hl : LocTy s o (.grow E))
    (hclear : s.truncate o 0 = .ok sClear)
    (hempty : sEval.read o = .ok (.resizable E #[]))
    (hwrite : sEval.write o (.resizable E es) = .ok s')
    (hitems : ∀ (i : Nat) (e : Val), es[i]? = some e → FlatTy E e) :
    StoreLeExcept (fun r => r = o.root) sEval s' ∧
      sClear.read o = .ok (.resizable E #[]) ∧
      sEval.read o = .ok (.resizable E #[]) ∧
      s'.read o = .ok (.resizable E es) ∧ LocTy s' o (.grow E) := by
  obtain ⟨_, _, _, hcleared, _⟩ :=
    clear_growshrink s sClear o E hl.grow_to_growshrink hclear
  have hwriteExcept : StoreLeExcept (fun r => r = o.root) sEval s' :=
    modify_roots_agree_except sEval s' o (fun _ => some (.resizable E es))
      (by simpa [Store.write] using hwrite)
  have hwritten : s'.read o = .ok (.resizable E es) :=
    write_read sEval s' o (.resizable E es) hwrite
  have hloc : LocTy s' o (.grow E) := by
    exact ⟨.resizable E es, hwritten, ⟨rfl, hitems⟩⟩
  exact ⟨hwriteExcept, hcleared, hempty, hwritten, hloc⟩

/-- `growshrink` whole assignment has the same clear-before-replacement
boundary as assignment to a `grow` owner. -/
theorem assignWhole_growshrink (s sClear sEval s' : Store) (o : Loc) (E : Ty)
    (es : Array Val) (hl : LocTy s o (.growshrink E))
    (hclear : s.truncate o 0 = .ok sClear)
    (hempty : sEval.read o = .ok (.resizable E #[]))
    (hwrite : sEval.write o (.resizable E es) = .ok s')
    (hitems : ∀ (i : Nat) (e : Val), es[i]? = some e → FlatTy E e) :
    StoreLeExcept (fun r => r = o.root) sEval s' ∧
      sClear.read o = .ok (.resizable E #[]) ∧
      sEval.read o = .ok (.resizable E #[]) ∧
      s'.read o = .ok (.resizable E es) ∧ LocTy s' o (.growshrink E) := by
  obtain ⟨_, _, _, hcleared, _⟩ := clear_growshrink s sClear o E hl hclear
  have hwriteExcept : StoreLeExcept (fun r => r = o.root) sEval s' :=
    modify_roots_agree_except sEval s' o (fun _ => some (.resizable E es))
      (by simpa [Store.write] using hwrite)
  have hwritten : s'.read o = .ok (.resizable E es) :=
    write_read sEval s' o (.resizable E es) hwrite
  have hloc : LocTy s' o (.growshrink E) := by
    exact ⟨.resizable E es, hwritten, ⟨rfl, hitems⟩⟩
  exact ⟨hwriteExcept, hcleared, hempty, hwritten, hloc⟩

private def limitedRetentionBefore : Val :=
  .limited (.int .i64) 4 #[.int .i64 10, .int .i64 20, .int .i64 30] 3
private def limitedRetentionAfterPop : Val :=
  .limited (.int .i64) 4 #[.int .i64 10, .int .i64 20, .int .i64 30] 2
private def limitedRetentionAfterGrowth : Val :=
  .limited (.int .i64) 4
    (limitedAppendSlots #[.int .i64 10, .int .i64 20, .int .i64 30]
      #[.int .i64 99] 2) 3
private def limitedRetentionSlot (i : Nat) : Loc := ⟨.global 0, [i]⟩
private def limitedRetentionAfterPopStore : Store :=
  ⟨({} : Std.HashMap RootInst Val).insert (.global 0) limitedRetentionAfterPop⟩
private def limitedRetentionAfterGrowthStore : Store :=
  ⟨({} : Std.HashMap RootInst Val).insert (.global 0) limitedRetentionAfterGrowth⟩

private theorem limitedRetentionPriorSlotsTyped :
    ∀ (i : Nat) (e : Val), #[Val.int .i64 10, .int .i64 20, .int .i64 30][i]? = some e →
      FlatTy (.int .i64) e := by
  intro i e he
  cases i with
  | zero => simp at he; subst e; simp [FlatTy]
  | succ i =>
    cases i with
    | zero => simp at he; subst e; simp [FlatTy]
    | succ i =>
      cases i with
      | zero => simp at he; subst e; simp [FlatTy]
      | succ i => simp_all

private theorem limitedRetentionAppendedSlotsTyped :
    ∀ (i : Nat) (e : Val), #[Val.int .i64 99][i]? = some e → FlatTy (.int .i64) e := by
  intro i e he
  cases i with
  | zero => simp at he; subst e; simp [FlatTy]
  | succ i => simp_all

private theorem limitedRetentionAfterPopSlot2Read :
    limitedRetentionAfterPopStore.read (limitedRetentionSlot 2) = .ok (.int .i64 30) := by
  simp [limitedRetentionAfterPopStore, Store.read, limitedRetentionSlot,
    limitedRetentionAfterPop, Val.get?, Val.children?, Val.elems?]

private theorem limitedRetentionAfterGrowthSlot2Read :
    limitedRetentionAfterGrowthStore.read (limitedRetentionSlot 2) = .ok (.int .i64 99) := by
  simp [Store.read, limitedRetentionAfterGrowthStore, limitedRetentionSlot,
    limitedRetentionAfterGrowth, Val.get?, Val.children?, Val.elems?]
  rw [limitedAppendSlots_get_appended #[.int .i64 10, .int .i64 20, .int .i64 30]
    #[.int .i64 99] 2 0 (by decide) (by decide)]
  rfl

private theorem limitedRetentionAfterGrowthSlot3Invalid :
    limitedRetentionAfterGrowthStore.read (limitedRetentionSlot 3) = .error .pathRange := by
  have hsize := limitedAppendSlots_size_eq
    #[.int .i64 10, .int .i64 20, .int .i64 30] #[.int .i64 99] 2
    (by decide) (by decide)
  simp [Store.read, limitedRetentionAfterGrowthStore, limitedRetentionSlot,
    limitedRetentionAfterGrowth, Val.get?, Val.children?, Val.elems?, hsize]

/-- A popped limited slot remains typed and readable, later growth overwrites
that same slot, and the next never-written capacity slot stays inaccessible. -/
theorem limited_retention_regression :
    Val.truncate 2 limitedRetentionBefore = some limitedRetentionAfterPop ∧
    FlatTy (.limited (.int .i64) 4) limitedRetentionAfterPop ∧
    limitedRetentionAfterPopStore.read (limitedRetentionSlot 2) = .ok (.int .i64 30) ∧
    LocTy limitedRetentionAfterPopStore (limitedRetentionSlot 2) (.int .i64) ∧
    Val.appendAll #[.int .i64 99] limitedRetentionAfterPop = some limitedRetentionAfterGrowth ∧
    limitedRetentionAfterGrowthStore.read (limitedRetentionSlot 2) = .ok (.int .i64 99) ∧
    LocTy limitedRetentionAfterGrowthStore (limitedRetentionSlot 2) (.int .i64) ∧
    FlatTy (.limited (.int .i64) 4) limitedRetentionAfterGrowth ∧
    limitedRetentionAfterGrowthStore.read (limitedRetentionSlot 3) = .error .pathRange := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [FlatTy, limitedRetentionAfterPop]
    exact ⟨trivial, trivial, by decide, by decide, limitedRetentionPriorSlotsTyped⟩
  · exact limitedRetentionAfterPopSlot2Read
  · exact ⟨.int .i64 30, limitedRetentionAfterPopSlot2Read, rfl⟩
  · exact appendAll_limited_shape (.int .i64) 4
      #[.int .i64 10, .int .i64 20, .int .i64 30] #[.int .i64 99] 2
      (by decide) (by decide)
  · exact limitedRetentionAfterGrowthSlot2Read
  · exact ⟨.int .i64 99, limitedRetentionAfterGrowthSlot2Read, rfl⟩
  · simp only [FlatTy, limitedRetentionAfterGrowth]
    have hsize := limitedAppendSlots_size_eq
      #[.int .i64 10, .int .i64 20, .int .i64 30] #[.int .i64 99] 2
      (by decide) (by decide)
    have hslots : 3 ≤ (limitedAppendSlots #[.int .i64 10, .int .i64 20, .int .i64 30]
        #[.int .i64 99] 2).size := by rw [hsize]; decide
    refine ⟨trivial, trivial, by decide, hslots, ?_⟩
    exact flat_limitedAppendSlots (.int .i64)
      #[.int .i64 10, .int .i64 20, .int .i64 30] #[.int .i64 99] 2
      (by decide) limitedRetentionPriorSlotsTyped limitedRetentionAppendedSlotsTyped
  · exact limitedRetentionAfterGrowthSlot3Invalid

theorem truncate_root_exists (s s' : Store) (o : Loc) (len : Nat)
    (h : s.truncate o len = .ok s') : s'.roots[o.root]? ≠ none := by
  have hm : s.modify o (Val.truncate len) = .ok s' := by
    simpa [Store.truncate] using h
  obtain ⟨old, x, y, new, hroot, hget, hnew, hmod, hroots⟩ :=
    modify_spec s s' o (Val.truncate len) hm
  rw [hroots]
  simp

theorem append_resizable_frame (s s' : Store) (o : Loc) (vs : Array Val) (n : Nat)
    (E : Ty) (hl : LocTy s o (.grow E))
    (h : s.append o vs = .ok (s', n)) :
    ∀ (l : Loc) (v : Val), s.read l = .ok v →
      ¬ (l.root = o.root ∧ l.path <+: o.path) → s'.read l = .ok v := by
  obtain ⟨es, hr, hn, hm⟩ := append_spec_grow s s' o vs n E hl h
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
  intro l v hv hn'
  obtain ⟨ol, hol, hgl⟩ := (read_ok_iff _ _ _).1 hv
  by_cases hlr : l.root = o.root
  · rw [hlr] at hol
    rw [ho] at hol; cases hol
    have hp : ¬ l.path <+: o.path := fun hp => hn' ⟨hlr, hp⟩
    exact (read_ok_iff _ _ _).2 ⟨new, by rw [hlr, hroots]; simp, (hkeep l.path v hgl).1 hp⟩
  · exact (read_ok_iff _ _ _).2 ⟨ol, by rw [other l hlr]; exact hol, hgl⟩

theorem append_except_owner (s s' : Store) (o : Loc) (vs : Array Val) (n : Nat)
    (h : s.append o vs = .ok (s', n)) :
    StoreLeExcept (fun r => r = o.root) s s' := by
  have hm : s.modify o (Val.appendAll vs) = .ok s' := by
    unfold Store.append at h
    cases hlen : s.length o with
    | error k => simp [hlen] at h
    | ok len =>
      simp only [hlen] at h
      cases hmod : s.modify o (Val.appendAll vs) with
      | error k => simp [hmod] at h
      | ok st =>
        have hp : st = s' ∧ len = n := by simpa [hmod] using h
        rcases hp with ⟨rfl, rfl⟩
        rfl
  obtain ⟨old, x, y, new, ho, hx, hy, hmod, hroots⟩ :=
    modify_spec s s' o (Val.appendAll vs) hm
  intro r hr
  rw [hroots]
  simp [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Ne.symm hr]

/-- Append preserves the existing read frame for resizable owners. Limited arrays
reuse hidden backing slots, so only their visible prefix keeps its contents. -/
theorem th_mem_01 (s s' : Store) (o : Loc) (vs : Array Val) (n : Nat)
    (howner :
      (∃ E, LocTy s o (.grow E) ∧
        ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e) ∨
      (∃ E, LocTy s o (.growshrink E) ∧
        ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e) ∨
      (∃ E capacity, E.flat = true ∧ LocTy s o (.limited E capacity) ∧
        ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e))
    (h : s.append o vs = .ok (s', n)) :
    StoreLe s s' ∧ StoreLeExcept (fun r => r = o.root) s s' ∧
    ((∃ E es, LocTy s' o (.grow E) ∧ s.read o = .ok (.resizable E es) ∧ n = es.size ∧
        (∀ (l : Loc) (v : Val), s.read l = .ok v →
          ¬ (l.root = o.root ∧ l.path <+: o.path) → s'.read l = .ok v) ∧
        (∀ (i : Nat) (e : Val), vs[i]? = some e →
          s'.read ⟨o.root, o.path ++ [n + i]⟩ = .ok e)) ∨
      (∃ E es, LocTy s' o (.growshrink E) ∧ s.read o = .ok (.resizable E es) ∧ n = es.size ∧
        (∀ (l : Loc) (v : Val), s.read l = .ok v →
          ¬ (l.root = o.root ∧ l.path <+: o.path) → s'.read l = .ok v) ∧
        (∀ (i : Nat) (e : Val), vs[i]? = some e →
          s'.read ⟨o.root, o.path ++ [n + i]⟩ = .ok e)) ∨
      (∃ E capacity slots len, E.flat = true ∧
        LocTy s' o (.limited E capacity) ∧ s.read o = .ok (.limited E capacity slots len) ∧
        n = len ∧ len ≤ slots.size ∧ len + vs.size ≤ capacity ∧
        (∀ (i : Nat) (e : Val), i < len → slots[i]? = some e →
          s'.read ⟨o.root, o.path ++ [i]⟩ = .ok e) ∧
        (∀ (i : Nat) (e : Val), vs[i]? = some e →
          s'.read ⟨o.root, o.path ++ [len + i]⟩ = .ok e))) := by
  have hexcept := append_except_owner s s' o vs n h
  rcases howner with hgrow | hgrowshrink | hlimited
  · obtain ⟨E, hl, hvs⟩ := hgrow
    obtain ⟨hle, hpost, es, hr, hn, happended⟩ := append_le s s' o vs n E hl hvs h
    have hframe := append_resizable_frame s s' o vs n E hl h
    exact ⟨hle, hexcept, Or.inl ⟨E, es, hpost, hr, hn, hframe, happended⟩⟩
  · obtain ⟨E, hl, hvs⟩ := hgrowshrink
    have hlgrow : LocTy s o (.grow E) := by
      obtain ⟨v, hread, htype⟩ := hl
      cases v <;> simp only [FlatTy] at htype ⊢
      exact ⟨_, hread, htype⟩
    obtain ⟨hle, hpost, es, hr, hn, happended⟩ :=
      append_le_growshrink s s' o vs n E hl hvs h
    have hframe := append_resizable_frame s s' o vs n E hlgrow h
    exact ⟨hle, hexcept, Or.inr (Or.inl ⟨E, es, hpost, hr, hn, hframe, happended⟩)⟩
  · obtain ⟨E, capacity, hE, hl, hvs⟩ := hlimited
    obtain ⟨hle, hpost, slots, len, hr, hn, hlen, hcap, happended, hvisible⟩ :=
      append_le_limited s s' o vs n E capacity hE hl hvs h
    exact ⟨hle, hexcept, Or.inr (Or.inr ⟨E, capacity, slots, len, hE, hpost, hr, hn,
      hlen, hcap, hvisible, happended⟩)⟩


/-! ### The live-reference invariant

A reference or slice is held only as the whole value of a variable. The
invariant says each one denotes a valid location of an array or flat type. It
is preserved by every memory operation of the evaluator: a type-preserving
write, growth, binding a fresh root, and releasing a scope's roots when no
surviving reference targets one of them. -/

/-- A slice denotes a run inside a valid array location. -/
def SliceOk (s : Store) (l : Loc) (st n : Nat) : Prop :=
  ∃ E, (∃ k, LocTy s l (.arr E k) ∧ st + n ≤ k) ∨
    ((LocTy s l (.grow E) ∨ LocTy s l (.growshrink E)) ∧
      ∃ E' es, s.read l = .ok (.resizable E' es) ∧ st + n ≤ es.size) ∨
    (∃ capacity slots len, LocTy s l (.limited E capacity) ∧
      s.read l = .ok (.limited E capacity slots len) ∧ st + n ≤ slots.size)

/-- A held value is a reference to a valid typed location, a slice of a valid
run, or holds no reference. -/
def HeldOk (s : Store) : Val → Prop
  | .ref l => ∃ T, T.refTarget = true ∧ LocTy s l T
  | .slice l st n => SliceOk s l st n
  | _ => True

/-- A held slice into the owner header also needs its run to fit the new length. -/
def ResizableRetainedHeld (o : Loc) (len : Nat) : Val → Prop
  | .ref l => RetainedLoc o len l
  | .slice l st n => RetainedLoc o len l ∧
      (l.root ≠ o.root ∨ l.path ≠ o.path ∨ st + n ≤ len)
  | _ => True

abbrev RetainedHeld := ResizableRetainedHeld

def LimitedRetainedHeld (o : Loc) (slots : Array Val) : Val → Prop
  | .ref l => LimitedRetainedLoc o slots l
  | .slice l st n => LimitedRetainedSlice o slots l st n
  | _ => True

def LiveRefs (s : Store) : Prop :=
  ∀ (r : RootInst) (v : Val), s.roots[r]? = some v → HeldOk s v

def LiveRefsOn (demanded : RootInst → Prop) (s : Store) : Prop :=
  ∀ (r : RootInst) (v : Val), demanded r → s.roots[r]? = some v → HeldOk s v

theorem SliceOk.mono {s s' : Store} {l : Loc} {st n : Nat} (hle : StoreLe s s')
    (h : SliceOk s l st n) : SliceOk s' l st n := by
  obtain ⟨E, h⟩ := h
  refine ⟨E, ?_⟩
  rcases h with ⟨k, hl, hk⟩ | hres | hlim
  · exact Or.inl ⟨k, LocTy.mono hle hl, hk⟩
  · rcases hres with ⟨hl, E', es, hr, hk⟩
    obtain ⟨old, ho, hg⟩ := (read_ok_iff _ _ _).1 hr
    obtain ⟨old', ho', href⟩ := hle _ _ ho
    obtain ⟨x', hx', hflat', hsize⟩ := href _ _ hg
    have hflat : FlatTy (.grow E) (.resizable E' es) ∨
        FlatTy (.growshrink E) (.resizable E' es) := by
      rcases hl with hgrow | hshrink
      · obtain ⟨v, hv, ht⟩ := hgrow
        rw [hr] at hv; cases hv
        exact Or.inl ht
      · obtain ⟨v, hv, ht⟩ := hshrink
        rw [hr] at hv; cases hv
        exact Or.inr ht
    rcases hflat with hflat | hflat
    · have hnew := hflat' (.grow E) hflat
      cases x' with
      | resizable E2 es2 =>
        simp only [FlatTy] at hnew
        rcases hnew with ⟨rfl, _⟩
        obtain ⟨es2', hes2, hsize'⟩ := hsize es (by simp [Val.elems?])
        simp only [Val.elems?, Option.some.injEq] at hes2
        cases hes2
        have hl' : LocTy s' l (.grow E) ∨ LocTy s' l (.growshrink E) :=
          hl.elim (fun h => Or.inl (LocTy.mono hle h))
            (fun h => Or.inr (LocTy.mono hle h))
        exact Or.inr (Or.inl ⟨hl', E, es2,
          (read_ok_iff _ _ _).2 ⟨old', ho', hx'⟩, by omega⟩)
      | _ => simp [FlatTy] at hnew
    · have hnew := hflat' (.growshrink E) hflat
      cases x' with
      | resizable E2 es2 =>
        simp only [FlatTy] at hnew
        rcases hnew with ⟨rfl, _⟩
        obtain ⟨es2', hes2, hsize'⟩ := hsize es (by simp [Val.elems?])
        simp only [Val.elems?, Option.some.injEq] at hes2
        cases hes2
        have hl' : LocTy s' l (.grow E) ∨ LocTy s' l (.growshrink E) :=
          hl.elim (fun h => Or.inl (LocTy.mono hle h))
            (fun h => Or.inr (LocTy.mono hle h))
        exact Or.inr (Or.inl ⟨hl', E, es2,
          (read_ok_iff _ _ _).2 ⟨old', ho', hx'⟩, by omega⟩)
      | _ => simp [FlatTy] at hnew
  · rcases hlim with ⟨capacity, slots, len, hl, hr, hk⟩
    obtain ⟨old, ho, hg⟩ := (read_ok_iff _ _ _).1 hr
    obtain ⟨old', ho', href⟩ := hle _ _ ho
    obtain ⟨x', hx', hflat', hsize⟩ := href _ _ hg
    have hflat : FlatTy (.limited E capacity) (.limited E capacity slots len) := by
      obtain ⟨v, hv, ht⟩ := hl
      rw [hr] at hv; cases hv
      exact ht
    have hnew := hflat' (.limited E capacity) hflat
    cases x' with
    | limited E2 capacity2 slots2 len2 =>
      simp only [FlatTy] at hnew
      rcases hnew with ⟨rfl, rfl, _, _, _⟩
      obtain ⟨slots', hslots, hsize'⟩ := hsize slots (by simp [Val.elems?])
      simp only [Val.elems?, Option.some.injEq] at hslots
      cases hslots
      refine Or.inr (Or.inr ⟨capacity, slots2, len2, LocTy.mono hle hl,
        (read_ok_iff _ _ _).2 ⟨old', ho', hx'⟩, ?_⟩)
      omega
    | _ => simp [FlatTy] at hnew

theorem SliceOk.truncate_limited {s s' : Store} {o l : Loc} {len st n : Nat}
    {E : Ty} {capacity : Nat} (hl : LocTy s o (.limited E capacity))
    (htruncate : s.truncate o len = .ok s') (hslice : SliceOk s l st n) :
    SliceOk s' l st n := by
  obtain ⟨hle, _, _⟩ := truncate_limited_le s s' o len E capacity hl htruncate
  exact hslice.mono hle

theorem HeldOk.mono {s s' : Store} {v : Val} (hle : StoreLe s s') (h : HeldOk s v) :
    HeldOk s' v := by
  cases v <;> simp only [HeldOk] at h ⊢
  · obtain ⟨T, hT, hl⟩ := h
    exact ⟨T, hT, LocTy.mono hle hl⟩
  · exact SliceOk.mono hle h

/-- Preserve held values when an operation supplies validity for every retained
reference target and slice base. A run over the resized owner header must fit
the new length; runs rooted in retained elements need no new bound. -/
theorem HeldOk.retain {s s' : Store} {o : Loc} {len : Nat} {v : Val}
    (hLoc : ∀ l T, RetainedLoc o len l → LocTy s l T → LocTy s' l T)
    (hSlice : ∀ l st n, RetainedLoc o len l →
      (l.root ≠ o.root ∨ l.path ≠ o.path ∨ st + n ≤ len) →
      SliceOk s l st n → SliceOk s' l st n)
    (hretained : RetainedHeld o len v) (h : HeldOk s v) : HeldOk s' v := by
  cases v <;> simp only [HeldOk, RetainedHeld] at hretained h ⊢
  · obtain ⟨T, hT, hl⟩ := h
    exact ⟨T, hT, hLoc _ _ hretained hl⟩
  · exact hSlice _ _ _ hretained.1 hretained.2 h

theorem HeldOk.retainLimited {s s' : Store} {o : Loc} {slots : Array Val} {v : Val}
    (hLoc : ∀ l T, LimitedRetainedLoc o slots l → LocTy s l T → LocTy s' l T)
    (hSlice : ∀ l st n, LimitedRetainedSlice o slots l st n →
      SliceOk s l st n → SliceOk s' l st n)
    (hretained : LimitedRetainedHeld o slots v) (h : HeldOk s v) : HeldOk s' v := by
  cases v <;> simp only [HeldOk, LimitedRetainedHeld] at hretained h ⊢
  · obtain ⟨T, hT, hl⟩ := h
    exact ⟨T, hT, hLoc _ _ hretained hl⟩
  · exact hSlice _ _ _ hretained h

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
  obtain ⟨es, hr, hn, hm⟩ := append_spec_grow s s' l vs n E hl h
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
      have hroot : s.read l = .ok old := by simp [Store.read, ho, hp, get_nil]
      rw [hroot] at hr
      cases old <;> simp [Val.appendAll] at hy hr
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
    rcases h with ⟨k, hl, hk⟩ | ⟨hl, E', es, hr, hk⟩ | ⟨capacity, slots, len, hl, hr, hk⟩
    · exact Or.inl ⟨k, locTy_agree hagree ht hl, hk⟩
    · exact Or.inr (Or.inl ⟨hl.elim (fun h => Or.inl (locTy_agree hagree ht h))
        (fun h => Or.inr (locTy_agree hagree ht h)), E', es, read_agree hagree ht hr, hk⟩)
    · exact Or.inr (Or.inr ⟨capacity, slots, len, locTy_agree hagree ht hl,
        read_agree hagree ht hr, hk⟩)

theorem liveRefsOn_except (s s' : Store) (demanded skipped : RootInst → Prop)
    (hagree : StoreLeExcept skipped s s')
    (hlr : LiveRefsOn demanded s)
    (hsurv : ∀ r v, demanded r → ¬ skipped r → s.roots[r]? = some v → TargetsOk skipped v)
    (hnew : ∀ r v, demanded r → skipped r → s'.roots[r]? = some v → HeldOk s' v) :
    LiveRefsOn demanded s' := by
  intro r v hd hv
  by_cases hs : skipped r
  · exact hnew r v hd hs hv
  · have hsrc : s.roots[r]? = some v := by rw [← hagree r hs]; exact hv
    exact heldOk_agree (fun r hr => hagree r hr) (hsurv r v hd hs hsrc) (hlr r v hd hsrc)

theorem liveRefsOn_preserve_except (s s' : Store) (demanded skipped : RootInst → Prop)
    (hagree : StoreLeExcept skipped s s')
    (hlr : LiveRefsOn demanded s)
    (hstable : ∀ r v, demanded r → ¬ skipped r → s.roots[r]? = some v →
      HeldOk s v → HeldOk s' v)
    (hnew : ∀ r v, demanded r → skipped r → s'.roots[r]? = some v → HeldOk s' v) :
    LiveRefsOn demanded s' := by
  intro r v hd hv
  by_cases hs : skipped r
  · exact hnew r v hd hs hv
  · have hsrc : s.roots[r]? = some v := by rw [← hagree r hs]; exact hv
    exact hstable r v hd hs hsrc (hlr r v hd hsrc)

/-- Keep demanded holders across an operation using its retained-target proof.
The caller separately establishes validity for holders rewritten by the operation. -/
theorem liveRefsOn_retain_except (s s' : Store) (demanded : RootInst → Prop)
    (o : Loc) (len : Nat) (hagree : StoreLeExcept (fun r => r = o.root) s s')
    (hlr : LiveRefsOn demanded s)
    (hretain : ∀ r v, demanded r → s.roots[r]? = some v → RetainedHeld o len v)
    (hLoc : ∀ l T, RetainedLoc o len l → LocTy s l T → LocTy s' l T)
    (hSlice : ∀ l st n, RetainedLoc o len l →
      (l.root ≠ o.root ∨ l.path ≠ o.path ∨ st + n ≤ len) →
      SliceOk s l st n → SliceOk s' l st n)
    (hnew : ∀ r v, demanded r → r = o.root → s'.roots[r]? = some v → HeldOk s' v) :
    LiveRefsOn demanded s' := by
  apply liveRefsOn_preserve_except s s' demanded (fun r => r = o.root) hagree hlr
  · intro r v hd hskip hv hheld
    exact HeldOk.retain hLoc hSlice (hretain r v hd hv) hheld
  · exact hnew

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

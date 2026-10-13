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
    | limited E capacity slots len =>
      rw [get_limited] at h1
      cases hi : slots[i]? with
      | none => simp [hi] at h1
      | some e =>
        simp only [hi, Option.bind_some] at h1
        obtain ⟨hlt, he⟩ := Array.getElem?_eq_some_iff.1 hi
        obtain ⟨e', he'⟩ := ih e x y h1 h2
        refine ⟨.limited E capacity (slots.set i e') len, ?_⟩
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
    | limited E capacity slots len =>
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
  obtain ⟨es, hr, hn, hm⟩ := append_spec_grow s s' l vs n E hl h
  refine flatStep_modify s s' l _ _ hm hr (by simp [IsRef]) ?_
  intro y hy
  simp only [Val.appendAll, Option.some.injEq] at hy
  subst hy
  exact ⟨by simp [IsRef], refines_push E es vs hvs⟩

theorem append_flatStep_growshrink (s s' : Store) (l : Loc) (vs : Array Val) (n : Nat) (E : Ty)
    (hl : LocTy s l (.growshrink E)) (hvs : ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e)
    (h : s.append l vs = .ok (s', n)) : FlatStep s s' := by
  obtain ⟨es, hr, _, hm⟩ := append_spec_growshrink s s' l vs n E hl h
  refine flatStep_modify s s' l _ _ hm hr (by simp [IsRef]) ?_
  intro y hy
  simp only [Val.appendAll, Option.some.injEq] at hy
  subst hy
  exact ⟨by simp [IsRef], refines_push E es vs hvs⟩

theorem append_flatStep_limited (s s' : Store) (l : Loc) (vs : Array Val) (n : Nat)
    (E : Ty) (capacity : Nat) (hE : E.flat = true) (hl : LocTy s l (.limited E capacity))
    (hvs : ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e)
    (h : s.append l vs = .ok (s', n)) : FlatStep s s' := by
  obtain ⟨slots, len, hr, _, hlen, hslots, hcap, hm⟩ :=
    append_spec_limited s s' l vs n E capacity hE hl hvs h
  refine flatStep_modify s s' l (Val.appendAll vs) (.limited E capacity slots len) hm hr
    (by simp [IsRef]) ?_
  intro y hy
  have hshape := appendAll_limited_shape E capacity slots vs len hlen hcap
  rw [hshape] at hy
  cases hy
  exact ⟨by simp [IsRef], refines_limitedAppend E capacity slots vs len hslots hvs hlen hcap hE⟩

theorem append_flatStep_owner (s s' : Store) (l : Loc) (vs : Array Val) (n : Nat)
    (owner E : Ty) (howner : owner.ownerElem? = some E) (hE : E.flat = true)
    (hl : LocTy s l owner) (hvs : ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e)
    (h : s.append l vs = .ok (s', n)) : FlatStep s s' := by
  cases owner with
  | grow E' =>
    have hE' : E' = E := by simpa [Ty.ownerElem?] using howner
    subst E
    exact append_flatStep _ _ _ _ _ _ hl hvs h
  | growshrink E' =>
    have hE' : E' = E := by simpa [Ty.ownerElem?] using howner
    subst E
    exact append_flatStep_growshrink _ _ _ _ _ _ hl hvs h
  | limited E' capacity =>
    have hE' : E' = E := by simpa [Ty.ownerElem?] using howner
    subst E
    exact append_flatStep_limited _ _ _ _ _ _ _ hE hl hvs h
  | _ => simp [Ty.ownerElem?] at howner

private theorem append_total_growshrink (s : Store) (l : Loc) (vs : Array Val) (E : Ty)
    (hl : LocTy s l (.growshrink E)) : ∃ s' n, s.append l vs = .ok (s', n) := by
  have hgrow : LocTy s l (.grow E) := by
    rcases hl with ⟨v, hread, hflat⟩
    cases v with
    | resizable E' es => exact ⟨_, hread, hflat⟩
    | _ => simp [FlatTy] at hflat
  exact append_total s l vs E hgrow

private theorem append_total_limited (s : Store) (l : Loc) (vs : Array Val) (E : Ty)
    (capacity : Nat) (slots : Array Val) (len : Nat)
    (hread : s.read l = .ok (.limited E capacity slots len)) (hlen : len ≤ slots.size)
    (hcapacity : len + vs.size ≤ capacity) : ∃ s' n, s.append l vs = .ok (s', n) := by
  let appended : Val := .limited E capacity (limitedAppendSlots slots vs len) (len + vs.size)
  have happended : Val.appendAll vs (.limited E capacity slots len) = some appended := by
    simpa [appended] using appendAll_limited_shape E capacity slots vs len hlen hcapacity
  obtain ⟨s', hmodify⟩ := modify_total s l (Val.appendAll vs)
    (.limited E capacity slots len) appended hread happended
  have hlength : s.length l = .ok len := by simp [Store.length, hread]
  exact ⟨s', len, by simp [Store.append, hlength, hmodify]⟩

private theorem checkAppendCapacity_resizable (l : Loc) (count : Nat) (org : OriginId)
    (s : St) (E : Ty) (es : Array Val)
    (hread : s.store.read l = .ok (.resizable E es)) :
    checkAppendCapacity l count org s = .ok () s := by
  change M.bind' (readLoc l) (fun v => match v with
    | .limited _ capacity _ len =>
      if capacity < len + count then abortAt .capacity org else pure ()
    | .resizable .. => pure ()
    | _ => fault .shape) s = .ok () s
  simp [M.bind', readLoc, hread]
  rfl

private theorem checkAppendCapacity_limited_fits (l : Loc) (count : Nat) (org : OriginId)
    (s : St) (E : Ty) (capacity : Nat) (slots : Array Val) (len : Nat)
    (hread : s.store.read l = .ok (.limited E capacity slots len))
    (hfits : len + count ≤ capacity) :
    checkAppendCapacity l count org s = .ok () s := by
  change M.bind' (readLoc l) (fun v => match v with
    | .limited _ cap _ n =>
      if cap < n + count then abortAt .capacity org else pure ()
    | .resizable .. => pure ()
    | _ => fault .shape) s = .ok () s
  simp [M.bind', readLoc, hread, Nat.not_lt_of_ge hfits]
  rfl

private theorem checkAppendCapacity_limited_overflow (l : Loc) (count : Nat) (org : OriginId)
    (s : St) (E : Ty) (capacity : Nat) (slots : Array Val) (len : Nat)
    (hread : s.store.read l = .ok (.limited E capacity slots len))
    (hoverflow : capacity < len + count) :
    checkAppendCapacity l count org s = .stop (.abort .capacity org) s := by
  change M.bind' (readLoc l) (fun v => match v with
    | .limited _ cap _ n =>
      if cap < n + count then abortAt .capacity org else pure ()
    | .resizable .. => pure ()
    | _ => fault .shape) s = .stop (.abort .capacity org) s
  simp [M.bind', readLoc, hread, hoverflow, abortAt]
  rfl

/-- A checked append either aborts at a limited owner's capacity or appends a
flat run. On success, the callback receives the concrete append step, which
preserves the typed store invariant for every owner kind. -/
theorem sat_checkedAppendLoc_bind {l : Loc} {vs : Array Val} {owner E : Ty} {org : OriginId}
    {s : St} {α : Type} {f : Nat → M α} {Q : α → St → Prop}
    (hl : LocTy s.store l owner) (howner : owner.ownerElem? = some E) (hE : E.flat = true)
    (hvs : ∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy E e)
    (k : ∀ s' i, s.store.append l vs = .ok (s', i) → FlatStep s.store s' →
      Sat (f i) { s with store := s' } Q) :
    Sat (checkedAppendLoc l vs org >>= f) s Q := by
  cases owner with
  | grow E' =>
    have hE' : E' = E := by simpa [Ty.ownerElem?] using howner
    subst E
    have hloc := hl
    rcases hl with ⟨v, hread, hflat⟩
    cases v with
    | resizable E'' es =>
      simp only [FlatTy] at hflat
      obtain ⟨rfl, hitems⟩ := hflat
      have hgrow : LocTy s.store l (.grow E') := ⟨_, hread, ⟨rfl, hitems⟩⟩
      obtain ⟨s', i, happ⟩ := append_total s.store l vs E' hgrow
      have hstep := append_flatStep_owner s.store s' l vs i (.grow E') E'
        (by simp [Ty.ownerElem?]) hE hloc hvs happ
      have hcheck := checkAppendCapacity_resizable l vs.size org s E' es hread
      have happend : appendLoc l vs s = .ok i { s with store := s' } := by
        simp [appendLoc, happ]
      have hrun : (checkedAppendLoc l vs org >>= f) s = f i { s with store := s' } := by
        change M.bind' (M.bind' (checkAppendCapacity l vs.size org)
          (fun _ => appendLoc l vs)) f s = _
        simp only [M.bind', hcheck, happend]
      unfold Sat
      rw [hrun]
      exact k s' i happ hstep
    | _ => simp [FlatTy] at hflat
  | growshrink E' =>
    have hE' : E' = E := by simpa [Ty.ownerElem?] using howner
    subst E
    have hloc := hl
    rcases hl with ⟨v, hread, hflat⟩
    cases v with
    | resizable E'' es =>
      simp only [FlatTy] at hflat
      obtain ⟨rfl, hitems⟩ := hflat
      obtain ⟨s', i, happ⟩ := append_total_growshrink s.store l vs E' hloc
      have hstep := append_flatStep_owner s.store s' l vs i (.growshrink E') E'
        (by simp [Ty.ownerElem?]) hE hloc hvs happ
      have hcheck := checkAppendCapacity_resizable l vs.size org s E' es hread
      have happend : appendLoc l vs s = .ok i { s with store := s' } := by
        simp [appendLoc, happ]
      have hrun : (checkedAppendLoc l vs org >>= f) s = f i { s with store := s' } := by
        change M.bind' (M.bind' (checkAppendCapacity l vs.size org)
          (fun _ => appendLoc l vs)) f s = _
        simp only [M.bind', hcheck, happend]
      unfold Sat
      rw [hrun]
      exact k s' i happ hstep
    | _ => simp [FlatTy] at hflat
  | limited E' capacity =>
    have hE' : E' = E := by simpa [Ty.ownerElem?] using howner
    subst E
    have hloc := hl
    rcases hl with ⟨v, hread, hflat⟩
    cases v with
    | limited E'' capacity' slots len =>
      simp only [FlatTy] at hflat
      obtain ⟨rfl, rfl, hlenCap, hlenSlots, hslots⟩ := hflat
      by_cases hcapacity : len + vs.size ≤ capacity
      · obtain ⟨s', i, happ⟩ := append_total_limited s.store l vs E' capacity
          slots len hread hlenSlots hcapacity
        have hstep := append_flatStep_owner s.store s' l vs i (.limited E' capacity) E'
          (by simp [Ty.ownerElem?]) hE hloc hvs happ
        have hcheck := checkAppendCapacity_limited_fits l vs.size org s E' capacity slots len
          hread hcapacity
        have happend : appendLoc l vs s = .ok i { s with store := s' } := by
          simp [appendLoc, happ]
        have hrun : (checkedAppendLoc l vs org >>= f) s = f i { s with store := s' } := by
          change M.bind' (M.bind' (checkAppendCapacity l vs.size org)
            (fun _ => appendLoc l vs)) f s = _
          simp only [M.bind', hcheck, happend]
        unfold Sat
        rw [hrun]
        exact k s' i happ hstep
      · have hoverflow : len + vs.size > capacity := Nat.lt_of_not_ge hcapacity
        have hcheck := checkAppendCapacity_limited_overflow l vs.size org s E' capacity slots len
          hread hoverflow
        have hrun : (checkedAppendLoc l vs org >>= f) s = .stop (.abort .capacity org) s := by
          change M.bind' (M.bind' (checkAppendCapacity l vs.size org)
            (fun _ => appendLoc l vs)) f s = _
          simp only [M.bind', hcheck]
        simp [Sat, hrun]
    | _ => simp [FlatTy] at hflat
  | _ => simp [Ty.ownerElem?] at howner

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
and the globals initialized so far hold values of their types. Global storage
never holds a reference, including roots outside the initialized declarations. -/
structure StoreInv (m : Module) (G : Nat) (s : St)
    (demanded : RootInst → Prop := fun _ => True) : Prop where
  live : ∀ (r : RootInst) (v : Val), s.store.roots[r]? = some v → demanded r → Held m G s.store v
  age : ∀ (r : RootInst) (v : Val), s.store.roots[r]? = some v → ∀ r', Targets v r' → Older r' r
  fresh : ∀ (a : ActId) (si : ScopeInst) (x : VarId), s.store.roots[RootInst.local a si x]? ≠ none → si < s.nextScope
  globals : ∀ (g : Nat) (gl : Global), g < G → m.globals[g]? = some gl → LocTy s.store ⟨.global g, []⟩ gl.ty
  globalNonRefs : ∀ (g : Nat) (v : Val), s.store.roots[RootInst.global g]? = some v → ¬ IsRef v

/-- A local root is live at a program point only while its binding is visible
and demanded by the remaining code. Globals stay live at every point. -/
def DemandedRoot (env : Env) (visible future : List VarId) : RootInst → Prop
  | .global _ => True
  | .local a si x => a = env.act ∧ x ∈ visible ∧ x ∈ future ∧
      ∃ lv, env.vars[x]? = some lv ∧ env.scopes.lookup lv.scope = some si

/-- The store invariant at a validated program point. Scope age and global
typing remain global facts; only local value validity follows demand. -/
abbrev StoreInvAt (m : Module) (G : Nat) (env : Env) (visible future : List VarId) (s : St) : Prop :=
  StoreInv m G s (DemandedRoot env visible future)

/-- A frame may narrow demand when the next syntax node becomes active. A
newly demanded root is harmless while it is absent from the store. -/
theorem StoreInv.changeDemand {m : Module} {G : Nat} {s : St}
    {oldDemand newDemand : RootInst → Prop} (hi : StoreInv m G s oldDemand)
    (hsub : ∀ r, newDemand r → oldDemand r ∨ s.store.roots[r]? = none) :
    StoreInv m G s newDemand := by
  refine ⟨?_, hi.age, hi.fresh, hi.globals, hi.globalNonRefs⟩
  intro r v hv hnew
  rcases hsub r hnew with hold | hfree
  · exact hi.live r v hv hold
  · rw [hfree] at hv
    cases hv

/-- Preserve the frame invariant across an operation that changes only roots in
`skipped`. The operation supplies the new facts for changed roots and proves
that references held by unchanged demanded roots remain valid. -/
theorem StoreInv.except {m : Module} {G : Nat} {s : St} {s' : Store}
    {demanded skipped : RootInst → Prop} (hi : StoreInv m G s demanded)
    (hagree : StoreLeExcept skipped s.store s')
    (hstable : ∀ r v, demanded r → ¬ skipped r → s.store.roots[r]? = some v →
      Held m G s.store v → Held m G s' v)
    (hnew : ∀ r v, demanded r → skipped r → s'.roots[r]? = some v → Held m G s' v)
    (hage : ∀ r v, skipped r → s'.roots[r]? = some v →
      ∀ r', Targets v r' → Older r' r)
    (hfresh : ∀ a si x, skipped (RootInst.local a si x) →
    s'.roots[RootInst.local a si x]? ≠ none → si < s.nextScope)
    (hglobals : ∀ g gl, skipped (.global g) → g < G → m.globals[g]? = some gl →
      LocTy s' ⟨.global g, []⟩ gl.ty)
    (hglobalNonRefs : ∀ g v, skipped (.global g) → s'.roots[RootInst.global g]? = some v →
      ¬ IsRef v) :
    StoreInv m G { s with store := s' } demanded := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r v hv hd
    by_cases hs : skipped r
    · exact hnew r v hd hs hv
    · have hvOld : s.store.roots[r]? = some v := by
        rw [hagree r hs] at hv
        exact hv
      exact hstable r v hd hs hvOld (hi.live r v hvOld hd)
  · intro r v hv r' ht
    by_cases hs : skipped r
    · exact hage r v hs hv r' ht
    · have hvOld : s.store.roots[r]? = some v := by
        rw [hagree r hs] at hv
        exact hv
      exact hi.age r v hvOld r' ht
  · intro a si x hv
    by_cases hs : skipped (RootInst.local a si x)
    · change s'.roots[RootInst.local a si x]? ≠ none at hv
      exact hfresh a si x hs hv
    · have hvOld : s.store.roots[RootInst.local a si x]? ≠ none := by
        rw [hagree (RootInst.local a si x) hs] at hv
        exact hv
      exact hi.fresh a si x hvOld
  · intro g gl hg hm
    by_cases hs : skipped (.global g)
    · exact hglobals g gl hs hg hm
    · exact LocTy.mono_except (hagree := hagree) hs (hi.globals g gl hg hm)
  · intro g v hv
    by_cases hs : skipped (.global g)
    · exact hglobalNonRefs g v hs hv
    · rw [hagree (.global g) hs] at hv
      exact hi.globalNonRefs g v hv

/-- A held value remains valid after truncation when every location it denotes
lies outside the removed suffix or in a retained element. -/
theorem Held.truncate {m : Module} {G : Nat} {s s' : Store}
    {o : Loc} {len : Nat} {v : Val}
    (htruncate : s.truncate o len = .ok s')
    (hagree : StoreLeExcept (fun r => r = o.root) s s')
    (hLoc : ∀ l T, RetainedLoc o len l → LocOk m G s l T → LocOk m G s' l T)
    (hSlice : ∀ l start count, RetainedLoc o len l →
      (l.root ≠ o.root ∨ l.path ≠ o.path ∨ start + count ≤ len) →
      ∀ E, SliceTy s l start count E → SliceTy s' l start count E)
    (hretained : RetainedHeld o len v) (h : Held m G s v) : Held m G s' v := by
  cases v with
  | ref l =>
    simp only [Held, RetainedHeld] at h hretained ⊢
    rcases h with ⟨T, htarget, hloc⟩ | ⟨hpath, hroot⟩
    · exact Or.inl ⟨T, htarget, hLoc l T hretained hloc⟩
    · refine Or.inr ⟨hpath, ?_⟩
      by_cases hsame : l.root = o.root
      · simpa [hsame] using truncate_root_exists s s' o len htruncate
      · have hunchanged : s'.roots[l.root]? = s.roots[l.root]? :=
          hagree l.root (by simpa using hsame)
        rw [hunchanged]
        exact hroot
  | slice l start count =>
    simp only [Held, RetainedHeld] at h hretained ⊢
    obtain ⟨E, hslice⟩ := h
    exact ⟨E, hSlice l start count hretained.1 hretained.2 E hslice⟩
  | _ => simp [Held]

/-- Rebuilding a value keeps a non-reference root when the replacement is
non-reference. -/
private theorem modifyAt_nonRef {v v' : Val} {path : List Nat}
    {f : Val → Option Val} (hmodify : v.modifyAt? path f = some v')
    (hresult : ∀ old value, f old = some value → ¬ IsRef value) : ¬ IsRef v' := by
  cases path with
  | nil => exact hresult v v' hmodify
  | cons index rest =>
    cases v <;> simp only [Val.modifyAt?] at hmodify
    all_goals first
      | contradiction
      | (split at hmodify
         · split at hmodify
           · simp only [Option.some.injEq] at hmodify
             cases hmodify
             simp [IsRef]
           · contradiction
         · contradiction)

/-- Truncation replaces its owner root with storage, including when the owner
is reached through an element path. -/
theorem truncate_ownerRoot_nonRef {s s' : Store} {o : Loc} {len : Nat} {v : Val}
    (htruncate : s.truncate o len = .ok s')
    (hvalue : s'.roots[o.root]? = some v) : ¬ IsRef v := by
  obtain ⟨old, x, y, new, _, _, _, hmodify, hroots⟩ :=
    modify_spec s s' o (Val.truncate len) htruncate
  have hnew : ¬ IsRef new := modifyAt_nonRef hmodify (by
    intro old value hresult
    cases old <;> simp only [Val.truncate] at hresult
    all_goals first
      | contradiction
      | (split at hresult
         · simp only [Option.some.injEq] at hresult
           cases hresult
           simp [IsRef]
         · contradiction))
  rw [hroots] at hvalue
  have sameValue : v = new := by simpa using hvalue.symm
  simpa [sameValue] using hnew

/-- Truncation preserves demanded holders when the demand analysis proves that
each holder remains inside the new logical extent. -/
theorem StoreInv.truncate {m : Module} {G : Nat} {s : St} {s' : Store}
    {demanded : RootInst → Prop} {o : Loc} {len : Nat}
    (hi : StoreInv m G s demanded)
    (htruncate : s.store.truncate o len = .ok s')
    (hretain : ∀ r v, demanded r → s.store.roots[r]? = some v → RetainedHeld o len v)
    (hLoc : ∀ l T, RetainedLoc o len l → LocOk m G s.store l T → LocOk m G s' l T)
    (hSlice : ∀ l start count, RetainedLoc o len l →
      (l.root ≠ o.root ∨ l.path ≠ o.path ∨ start + count ≤ len) →
      ∀ E, SliceTy s.store l start count E → SliceTy s' l start count E)
    (hnew : ∀ r v, demanded r → r = o.root → s'.roots[r]? = some v → Held m G s' v)
    (hage : ∀ r v, r = o.root → s'.roots[r]? = some v →
      ∀ r', Targets v r' → Older r' r)
    (hfresh : ∀ a si x, RootInst.local a si x = o.root →
      s'.roots[RootInst.local a si x]? ≠ none → si < s.nextScope)
    (hglobals : ∀ g gl, RootInst.global g = o.root →
      g < G → m.globals[g]? = some gl → LocTy s' ⟨.global g, []⟩ gl.ty) :
    StoreInv m G { s with store := s' } demanded := by
  apply StoreInv.except hi (truncate_except_owner s.store s' o len htruncate)
  · intro r old hd hskip hold hheld
    exact Held.truncate htruncate (truncate_except_owner s.store s' o len htruncate)
      hLoc hSlice (hretain r old hd hold) hheld
  · exact hnew
  · exact hage
  · exact hfresh
  · exact hglobals
  · intro g v hroot hv
    exact truncate_ownerRoot_nonRef htruncate (by simpa [← hroot] using hv)

theorem StoreInv.flatStep {m : Module} {G : Nat} {s : St} {st' : Store}
    {demanded : RootInst → Prop} (hi : StoreInv m G s demanded) (h : FlatStep s.store st') :
    StoreInv m G { s with store := st' } demanded := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r v hv hdem
    rcases h.back r v hv with h0 | ⟨hn, _⟩
    · exact (hi.live r v h0 hdem).mono h.le
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
  · intro g v hv
    rcases h.back (.global g) v hv with old | ⟨nonref, _⟩
    · exact hi.globalNonRefs g v old
    · exact nonref

/-- Binding a root that was absent. -/
theorem StoreInv.bind {m : Module} {G : Nat} {s : St} {r : RootInst} {v : Val}
    {demanded : RootInst → Prop} (hi : StoreInv m G s demanded)
    (hfree : s.store.roots[r]? = none) (hv : Held m G s.store v)
    (hage : ∀ r', Targets v r' → Older r' r)
    (hfr : ∀ a si x, r = .local a si x → si < s.nextScope)
    (hglobal : ∀ g, r = .global g → ¬ IsRef v) :
    StoreInv m G { s with store := s.store.introduce r v } demanded := by
  have hle := introduce_le s.store r v hfree
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r1 v1 h1 hdem
    rw [get_introduce] at h1
    by_cases hr : r = r1
    · simp only [hr, if_true, Option.some.injEq] at h1
      subst h1; exact hv.mono hle
    · simp only [hr, if_false] at h1
      exact (hi.live r1 v1 h1 hdem).mono hle
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
  · intro g value present
    rw [get_introduce] at present
    by_cases root : r = .global g
    · simp only [root, if_true, Option.some.injEq] at present
      subst value
      exact hglobal g root
    · simp only [root, if_false] at present
      exact hi.globalNonRefs g value present

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
    {demanded : RootInst → Prop} (hi : StoreInv m G s demanded)
    (ho : s.store.roots[r]? = some old) (hold : IsRef old)
    (hv : Held m G s.store v) (hage : ∀ r', Targets v r' → Older r' r) :
    StoreInv m G { s with store := ⟨(s.store.roots.erase r).insert r v⟩ } demanded := by
  have hle := rebind_le s.store r old v ho hold
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r1 v1 h1 hdem
    simp only [get_reinsert] at h1
    by_cases hr : r = r1
    · simp only [hr, if_true, Option.some.injEq] at h1
      subst h1; exact hv.mono hle
    · simp only [hr, if_false] at h1
      exact (hi.live r1 v1 h1 hdem).mono hle
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
  · intro g value present
    have root : r ≠ .global g := by
      intro equal
      subst r
      exact hi.globalNonRefs g old ho hold
    simp only [get_reinsert, root, if_false] at present
    exact hi.globalNonRefs g value present

end Goose.Core.Sound

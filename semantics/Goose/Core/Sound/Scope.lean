import Goose.Core.Sound.CallPreservation
import Goose.Core.Sound.Retain

/-!
How the frame changes when a variable is bound or rebound, when a call
returns, and when a block is entered and left.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

theorem lookup_cons (k b a : Nat) (l : List (Nat × Nat)) :
    ((k, b) :: l).lookup a = if a = k then some b else l.lookup a := by
  by_cases h : a = k
  · simp [List.lookup, h]
  · have hb : (a == k) = false := by simpa using h
    simp [List.lookup, hb, h]

theorem lookup_mem : ∀ (l : List (Nat × Nat)) (a b : Nat), l.lookup a = some b → (a, b) ∈ l
  | [], a, b, h => by simp [List.lookup] at h
  | (k, c) :: l, a, b, h => by
    rw [lookup_cons] at h
    by_cases hk : a = k
    · simp only [hk, if_true, Option.some.injEq] at h
      subst h; subst hk; exact List.mem_cons_self
    · simp only [hk, if_false] at h
      exact List.mem_cons_of_mem _ (lookup_mem l a b h)

theorem lookup_key {l : List (Nat × Nat)} {a b : Nat} (h : l.lookup a = some b) :
    a ∈ l.map Prod.fst :=
  List.mem_map.2 ⟨(a, b), lookup_mem l a b h, rfl⟩

/-- In a chain of scope instances that decrease outward, a scope at least as
far out has an instance no younger. -/
theorem lookup_idx_le : ∀ (l : List (Nat × Nat)), l.Pairwise (fun a b => b.2 < a.2) →
    ∀ sx sy six siy, l.lookup sx = some six → l.lookup sy = some siy →
      (l.map Prod.fst).idxOf sx ≤ (l.map Prod.fst).idxOf sy → siy ≤ six
  | [], _, sx, sy, six, siy, h, _, _ => by simp [List.lookup] at h
  | (k, c) :: l, hp, sx, sy, six, siy, h1, h2, h3 => by
    rw [lookup_cons] at h1 h2
    simp only [List.map_cons, List.idxOf_cons] at h3
    obtain ⟨hhd, htl⟩ := List.pairwise_cons.1 hp
    by_cases hx : sx = k
    · simp only [hx, if_true, Option.some.injEq] at h1
      subst h1
      by_cases hy : sy = k
      · simp only [hy, if_true, Option.some.injEq] at h2
        omega
      · simp only [hy, if_false] at h2
        have := hhd _ (lookup_mem l sy siy h2)
        simp at this; omega
    · simp only [hx, if_false] at h1
      by_cases hy : sy = k
      · have hx' : ¬ k = sx := fun e => hx e.symm
        simp [hy, hx'] at h3
      · simp only [hy, if_false] at h2
        have hx' : ¬ k = sx := fun e => hx e.symm
        have hy' : ¬ k = sy := fun e => hy e.symm
        simp only [beq_iff_eq, hx', hy', if_false] at h3
        exact lookup_idx_le l htl sx sy six siy h1 h2 (by omega)

variable {m : Module} {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}

theorem Frame.inst_lt {future : List VarId} (h : Frame m W tenv penv env s future) {sc si : Nat}
    (hl : env.scopes.lookup sc = some si) : W.base ≤ si ∧ si < s.nextScope :=
  h.below _ (lookup_mem _ _ _ hl)

/-- What denotes a root of the activation or of a caller was handed out
before the next scope instance. -/
theorem Frame.gam_older {future : List VarId} (h : Frame m W tenv penv env s future)
    {rho : List RootRef} {r : RootInst}
    (hg : Gam env W.P rho r) : ∀ a si x, r = RootInst.local a si x → si < s.nextScope := by
  intro a si x hr
  obtain ⟨q, _, hq⟩ := hg
  cases q with
  | «local» y =>
    obtain ⟨lv, si', _, hl, rfl⟩ := hq
    cases hr
    exact (h.inst_lt hl).2
  | global g => simp only [RootIn] at hq; subst hq; cases hr
  | param j =>
    subst hr
    exact Nat.lt_of_lt_of_le (h.pAge j a si x hq) h.base_le

/-- Binding a variable of an open block whose root was absent. -/
theorem Frame.bind {future : List VarId} (h : Frame m W tenv penv env s future)
    {x : VarId} {lv : LocalVar} {si : ScopeInst}
    {v : Val} (hx : env.vars[x]? = some lv) (hsi : env.scopes.lookup lv.scope = some si)
    (hst : lv.ty.paramOk = true)
    (hfree : s.store.roots[RootInst.local env.act si x]? = none)
    (hv : HasTy m W.G s.store v lv.ty)
    (hroot : ∀ r, Targets v r → (∃ ann, penv.ann x = some ann ∧ Gam env W.P ann r) ∧
      Older r (.local env.act si x)) :
    Frame m W { tenv with visible := x :: tenv.visible } penv env
      { s with store := s.store.introduce (.local env.act si x) v } (x :: future) := by
  have hle := introduce_le s.store (.local env.act si x) v hfree
  have hInv : StoreInv m W.G s (DemandedRoot env (x :: tenv.visible) (x :: future)) := by
    apply h.inv.changeDemand
    intro r hdem
    cases r with
    | global g => exact Or.inl trivial
    | «local» a si' x' =>
      rcases hdem with ⟨ha, hx', hf, lv', hvar, hlk'⟩
      by_cases hxx : x' = x
      · subst x'
        rw [hx] at hvar
        have hlv : lv' = lv := Option.some.inj hvar.symm
        have hsi' : si' = si := by
          rw [hlv] at hlk'
          exact (Option.some.inj (hsi.symm.trans hlk')).symm
        subst lv'
        subst si'
        subst a
        exact Or.inr hfree
      · have hxold : x' ∈ tenv.visible := by
          rcases List.mem_cons.1 hx' with h | h
          · exact absurd h hxx
          · exact h
        have hfuture : x' ∈ future := by
          rcases List.mem_cons.1 hf with h | h
          · exact absurd h hxx
          · exact h
        exact Or.inl ⟨ha, hxold, hfuture, lv', hvar, hlk'⟩
  exact
  { h with
    below := h.below, base_le := h.base_le
    vis := by
      intro x' hx'
      intro hfuture
      by_cases hxx : x' = x
      · subst hxx
        exact ⟨lv, si, v, hx, hsi, hst, by simp [get_introduce], hv.mono hle⟩
      · have hx'' : x' ∈ tenv.visible := by
          rcases List.mem_cons.1 hx' with e | e
          · exact absurd e hxx
          · exact e
        have hfuture' : x' ∈ future := by
          rcases List.mem_cons.1 hfuture with e | e
          · exact absurd e hxx
          · exact e
        obtain ⟨lv', si', v', h1, h2, h3, h4, h5⟩ := h.vis x' hx'' hfuture'
        refine ⟨lv', si', v', h1, h2, h3, ?_, h5.mono hle⟩
        rw [get_introduce]
        have : ¬ (RootInst.local env.act si x = RootInst.local env.act si' x') := by
          intro e; cases e; exact hxx rfl
        simp [this, h4]
    bindings := by
      intro x' hx'
      by_cases hxx : x' = x
      · subst x'
        refine ⟨lv, si, v, hx, hsi, hst, by simp [get_introduce], ?_⟩
        intro href
        exact hv.isRef href
      · have hxold : x' ∈ tenv.visible := by
          rcases List.mem_cons.1 hx' with heq | heq
          · exact absurd heq hxx
          · exact heq
        obtain ⟨lv', si', v', hvar, hlookup, hparam, hroot, hshape⟩ := h.bindings x' hxold
        refine ⟨lv', si', v', hvar, hlookup, hparam, ?_, hshape⟩
        rw [get_introduce]
        have hneq : ¬ (RootInst.local env.act si x = RootInst.local env.act si' x') := by
          intro heq; cases heq; exact hxx rfl
        simp [hneq, hroot]
    rooted := by
      intro x' lv' si' v' h1 h2 h3 r ht
      rw [get_introduce] at h3
      by_cases e : RootInst.local env.act si x = RootInst.local env.act si' x'
      · simp only [e, if_true, Option.some.injEq] at h3
        subst h3
        cases e
        exact (hroot r ht).1
      · simp only [e, if_false] at h3
        exact h.rooted x' lv' si' v' h1 h2 h3 r ht
    inv := hInv.bind hfree hv.held (fun r ht => (hroot r ht).2)
      (fun a si' x' e => by cases e; exact (h.inst_lt hsi).2)
    storage := by
      intro r T hstorage v' hpost
      by_cases hnew : r = RootInst.local env.act si x
      · subst r
        obtain ⟨x', lv', si', hvar', hlk', hroot', hnonref, hT⟩ := hstorage
        simp only [RootInst.local.injEq] at hroot'
        rcases hroot' with ⟨_, hsiEq, hxEq⟩
        subst x'
        subst si'
        have hlv : lv' = lv := Option.some.inj (hvar'.symm.trans hx)
        subst lv'
        subst T
        rw [get_introduce] at hpost
        simp at hpost
        subst v'
        have hstorable : lv.ty.storable = true := Ty.storable_of_paramOk_nonref hst hnonref
        have hflat := HasTy.flatOfStorableNonref hv hstorable hnonref
        exact ⟨v, by simp [Store.read, get_introduce, get_nil], hflat⟩
      · have hneq : ¬ (RootInst.local env.act si x = r) := by
          intro heq
          exact hnew heq.symm
        have hpre : s.store.roots[r]? = some v' := by
          rw [get_introduce] at hpost
          simpa [hneq] using hpost
        exact LocTy.mono hle (h.storage r T hstorage v' hpre)
    sa := by
      intro r E hd
      obtain ⟨v0, h1, h2, h3⟩ := h.sa r E hd
      refine ⟨v0, ?_, h2.mono hle, h3⟩
      rw [get_introduce]
      have hne : ¬ (RootInst.local env.act si x = r) := by
        rintro rfl; rw [hfree] at h1; cases h1
      simp [hne, h1] }

/-- Replacing the reference a visible variable holds. -/
theorem Frame.rebind {future : List VarId} (h : Frame m W tenv penv env s future)
    {x : VarId} {lv : LocalVar} {si : ScopeInst}
    {old v : Val} (hx : env.vars[x]? = some lv) (hsi : env.scopes.lookup lv.scope = some si)
    (ho : s.store.roots[RootInst.local env.act si x]? = some old) (hold : IsRef old)
    (hparam : lv.ty.paramOk = true)
    (hv : HasTy m W.G s.store v lv.ty)
    (hroot : ∀ r, Targets v r → (∃ ann, penv.ann x = some ann ∧ Gam env W.P ann r) ∧
      Older r (.local env.act si x)) :
    Frame m W tenv penv env
      { s with store := ⟨(s.store.roots.erase (.local env.act si x)).insert (.local env.act si x) v⟩ }
      future := by
  have hle := rebind_le s.store (.local env.act si x) old v ho hold
  exact
  { h with
    below := h.below, base_le := h.base_le
    vis := by
      intro x' hx'
      intro hfuture
      obtain ⟨lv', si', v', h1, h2, h3, h4, h5⟩ := h.vis x' hx' hfuture
      by_cases e : RootInst.local env.act si x = RootInst.local env.act si' x'
      · cases e
        rw [hx] at h1; cases h1
        exact ⟨lv, si, v, hx, hsi, h3, by simp [get_reinsert], hv.mono hle⟩
      · exact ⟨lv', si', v', h1, h2, h3, by simp [get_reinsert, e, h4], h5.mono hle⟩
    bindings := by
      intro x' hx'
      obtain ⟨lv', si', old', hvar', hlk', hparam', hroot', hshape'⟩ := h.bindings x' hx'
      by_cases heq : RootInst.local env.act si x = RootInst.local env.act si' x'
      · simp only [RootInst.local.injEq] at heq
        rcases heq with ⟨_, hsi', hxEq⟩
        subst hxEq
        subst si'
        have hlv : lv' = lv := Option.some.inj (hvar'.symm.trans hx)
        subst lv'
        refine ⟨lv, si, v, hx, hsi, hparam, by simp [get_reinsert], ?_⟩
        intro href
        exact hv.isRef href
      · refine ⟨lv', si', old', hvar', hlk', hparam', ?_, hshape'⟩
        simp [get_reinsert, heq, hroot']
    rooted := by
      intro x' lv' si' v' h1 h2 h3 r ht
      simp only [get_reinsert] at h3
      by_cases e : RootInst.local env.act si x = RootInst.local env.act si' x'
      · simp only [e, if_true, Option.some.injEq] at h3
        subst h3
        cases e
        exact (hroot r ht).1
      · simp only [e, if_false] at h3
        exact h.rooted x' lv' si' v' h1 h2 h3 r ht
    storage := by
      intro r' T hstorage v' hpost
      by_cases heq : r' = RootInst.local env.act si x
      · subst r'
        exact LocTy.mono hle (h.storage _ _ hstorage old ho)
      · have hpre : s.store.roots[r']? = some v' := by
          simp only [get_reinsert] at hpost
          have hneq : ¬ (RootInst.local env.act si x = r') := fun e => heq e.symm
          simpa [hneq] using hpost
        exact LocTy.mono hle (h.storage r' T hstorage v' hpre)
    inv := h.inv.rebind ho hold hv.held (fun r ht => (hroot r ht).2)
    sa := by
      intro r E hd
      obtain ⟨v0, h1, h2, h3⟩ := h.sa r E hd
      refine ⟨v0, ?_, h2.mono hle, h3⟩
      have hne : ¬ (RootInst.local env.act si x = r) := by
        rintro rfl
        obtain ⟨a, si', x', e, hlt⟩ := h.dOut _ E hd
        cases e
        exact absurd (h.inst_lt hsi).1 (Nat.not_le.2 hlt)
      simp [get_reinsert, hne, h1] }

theorem hasTy_slice_mu {G : Nat} {st : Store} {v : Val} {mu mu' : Mutability} {E : Ty}
    (h : HasTy m G st v (.slice mu E)) : HasTy m G st v (.slice mu' E) := h

/-- A call keeps the frame: the callee left every stored reference alone,
except the slices in the slice variables `D'` it was given references to, and
those it left typed and rooted within what each variable allows. -/
theorem Frame.outer {s' : St} {D' : RootInst → Ty → Prop} {A' : RootInst → RootInst → Prop}
    {future future' : List VarId} (h : Frame m W tenv penv env s future)
    (he : Ext [] (fun r => ∃ E, D' r E) s s')
    (hi : StoreInvAt m W.G env tenv.visible future' s')
    (hfuture : ∀ x, x ∈ future' → x ∈ future)
    (hsa : ∀ r E, D' r E → ∃ v, s'.store.roots[r]? = some v ∧
      HasTy m W.G s'.store v (.slice .mutable E) ∧ ∀ t, Targets v t → A' r t)
    (hD : ∀ r E, D' r E → (W.D r E ∧ ∀ t, A' r t → W.A r t) ∨
      (∃ x lv si mu, env.vars[x]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
        r = RootInst.local env.act si x ∧ lv.ty = .slice mu E ∧
        ∀ t, A' r t → ∃ ann, penv.ann x = some ann ∧ Gam env W.P ann t))
      (hDall : ∀ r E, W.D r E → D' r E) : Frame m W tenv penv env s' future' := by
  -- A root of this activation is no slice variable of a caller.
  have hfr : ∀ {x : VarId} {sc si : Nat} {E : Ty}, env.scopes.lookup sc = some si →
      ¬ W.D (RootInst.local env.act si x) E := by
    intro x sc si E hl hd
    obtain ⟨a, si', x', e, hlt⟩ := h.dOut _ E hd
    cases e
    exact absurd (h.inst_lt hl).1 (Nat.not_le.2 hlt)
  exact
  { h with
    below := fun p hp => ⟨(h.below p hp).1, Nat.lt_of_lt_of_le (h.below p hp).2 he.next⟩
    base_le := Nat.le_trans h.base_le he.next
    vis := by
      intro x hx
      intro hfut
      obtain ⟨lv, si, v, h1, h2, h3, h4, h5⟩ := h.vis x hx (hfuture x hfut)
      by_cases hd : ∃ E, D' (RootInst.local env.act si x) E
      · obtain ⟨E, hd⟩ := hd
        obtain ⟨v', g1, g2, _⟩ := hsa _ E hd
        rcases hD _ E hd with ⟨k, _⟩ | ⟨x', lv', si', mu, k1, k2, k3, k4, _⟩
        · exact absurd k (hfr h2)
        · cases k3
          rw [h1] at k1; cases k1
          exact ⟨lv, si, v', h1, h2, h3, g1, by rw [k4]; exact hasTy_slice_mu g2⟩
      · obtain ⟨v', h6, h7⟩ := hasTy_step he.le (fun hr => he.keep _ v h4 hr (by simp) hd) h3 h4 h5
        exact ⟨lv, si, v', h1, h2, h3, h6, h7⟩
    bindings := by
      intro x hx
      obtain ⟨lv, si, old, hvar, hlk, hparam, hroot, hshape⟩ := h.bindings x hx
      have hpostNe : s'.store.roots[RootInst.local env.act si x]? ≠ none :=
        dom_mono he.le (by rw [hroot]; simp)
      obtain ⟨v, hpost⟩ := Option.ne_none_iff_exists'.1 hpostNe
      refine ⟨lv, si, v, hvar, hlk, hparam, hpost, ?_⟩
      intro htype
      have hold : IsRef old := hshape htype
      by_cases hd : ∃ E, D' (RootInst.local env.act si x) E
      · obtain ⟨E, hd⟩ := hd
        obtain ⟨v', hpostSlice, htypeSlice, _⟩ := hsa _ E hd
        have hv : v' = v := Option.some.inj (hpostSlice.symm.trans hpost)
        subst v'
        exact htypeSlice.isRef (by simp [Ty.isRefLike])
      · have hkeep := he.keep _ old hroot hold (by simp) hd
        rw [hpost] at hkeep
        cases hkeep
        exact hold
    storage := by
      intro r T hstorage v hpost
      have hpreNe : s.store.roots[r]? ≠ none := he.dom r (by rw [hpost]; simp)
      cases hroot : s.store.roots[r]? with
      | none => exact False.elim (hpreNe hroot)
      | some old => exact LocTy.mono he.le (h.storage r T hstorage old hroot)
    rooted := by
      intro x lv si v h1 h2 h3 r ht
      by_cases hd : ∃ E, D' (RootInst.local env.act si x) E
      · obtain ⟨E, hd⟩ := hd
        obtain ⟨v', g1, _, g3⟩ := hsa _ E hd
        rw [h3] at g1; cases g1
        rcases hD _ E hd with ⟨k, _⟩ | ⟨x', lv', si', mu, k1, k2, k3, k4, k5⟩
        · exact absurd k (hfr h2)
        · cases k3
          exact k5 r (g3 r ht)
      · exact h.rooted x lv si v h1 h2 (he.back _ v h3 ht.isRef (by simp) hd) r ht
    inv := hi
    sa := by
      intro r E hd
      have hd' := hDall r E hd
      obtain ⟨v', g1, g2, g3⟩ := hsa r E hd'
      refine ⟨v', g1, g2, fun t ht => ?_⟩
      rcases hD r E hd' with ⟨_, k⟩ | ⟨x', lv', si', mu, k1, k2, k3, _⟩
      · exact k t (g3 t ht)
      · subst k3; exact absurd hd (hfr k2) }

/-- Reconstruct the demanded caller frame after a call that may shrink owners.
Only demanded bindings need typed-root preservation; the footprint preserves
annotations for unchanged references and explicit slice facts cover rebinding. -/
theorem Frame.outerPreserved {s' : St}
    {D' : RootInst → Ty → Prop} {A' : RootInst → RootInst → Prop}
    {future future' : List VarId} (h : Frame m W tenv penv env s future)
    (he : Footprint [] (fun r => ∃ E, D' r E) s s')
    (ht : PreservesRootTypes m W.G
      (CallerRootTypes W tenv env s.store future') s.store s'.store)
    (hi : StoreInvAt m W.G env tenv.visible future' s')
    (hfuture : ∀ x, x ∈ future' → x ∈ future)
    (hsa : ∀ r E, D' r E → ∃ v, s'.store.roots[r]? = some v ∧
      HasTy m W.G s'.store v (.slice .mutable E) ∧ ∀ t, Targets v t → A' r t)
    (hD : ∀ r E, D' r E → (W.D r E ∧ ∀ t, A' r t → W.A r t) ∨
      (∃ x lv si mu, env.vars[x]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
        r = RootInst.local env.act si x ∧ lv.ty = .slice mu E ∧
        ∀ t, A' r t → ∃ ann, penv.ann x = some ann ∧ Gam env W.P ann t))
    (hDall : ∀ r E, W.D r E → D' r E) : Frame m W tenv penv env s' future' := by
  have hstorageTypes := CallerRootTypes.preservesStorage ht
  have hfr : ∀ {x : VarId} {sc si : Nat} {E : Ty}, env.scopes.lookup sc = some si →
      ¬ W.D (RootInst.local env.act si x) E := by
    intro x sc si E hl hd
    obtain ⟨a, si', x', e, hlt⟩ := h.dOut _ E hd
    cases e
    exact absurd (h.inst_lt hl).1 (Nat.not_le.2 hlt)
  exact
  { h with
    below := fun p hp => ⟨(h.below p hp).1, Nat.lt_of_lt_of_le (h.below p hp).2 he.next⟩
    base_le := Nat.le_trans h.base_le he.next
    vis := by
      intro x hx hfut
      obtain ⟨lv, si, v, h1, h2, h3, h4, h5⟩ := h.vis x hx (hfuture x hfut)
      obtain ⟨v', h6, h7⟩ := ht _ lv.ty
        (Or.inl (Or.inl ⟨x, lv, si, hx, hfut, h1, h2, rfl, rfl⟩)) v h4 h5
      exact ⟨lv, si, v', h1, h2, h3, h6, h7⟩
    bindings := by
      intro x hx
      obtain ⟨lv, si, old, hvar, hlk, hparam, hroot, hshape⟩ := h.bindings x hx
      by_cases href : lv.ty.isRefLike = true
      · by_cases hd : ∃ E, D' (RootInst.local env.act si x) E
        · obtain ⟨E, hd⟩ := hd
          obtain ⟨v, hpost, htype, _⟩ := hsa _ E hd
          refine ⟨lv, si, v, hvar, hlk, hparam, hpost, ?_⟩
          intro _
          exact htype.isRef (by simp [Ty.isRefLike])
        · have hkeep := he.keep _ old hroot (hshape href) (by simp) hd
          exact ⟨lv, si, old, hvar, hlk, hparam, hkeep, fun _ => hshape href⟩
      · have hnonref : lv.ty.isRefLike = false := Bool.eq_false_iff.mpr href
        have hstorage' : StorageRootTypes env (RootInst.local env.act si x) lv.ty :=
          ⟨x, lv, si, hvar, hlk, rfl, hnonref, rfl⟩
        have hloc := h.storage _ _ hstorage' old hroot
        obtain ⟨oldValue, hrootOld, htypeOld⟩ := LocTy.hasTyRoot hloc hnonref
        obtain ⟨newValue, hrootNew, htypeNew⟩ :=
          hstorageTypes _ lv.ty hstorage' oldValue hrootOld htypeOld
        refine ⟨lv, si, newValue, hvar, hlk, hparam, hrootNew, ?_⟩
        intro htype
        rw [hnonref] at htype
        cases htype
    storage := by
      intro r T hstorage v' hpost
      have hpreNe : s.store.roots[r]? ≠ none := he.dom r (by rw [hpost]; simp)
      cases hroot : s.store.roots[r]? with
      | none => exact False.elim (hpreNe hroot)
      | some old =>
        rcases hstorage with ⟨x, lv, si, hvar, hlk, hrootType, hn, hT⟩
        have hstorage' : StorageRootTypes env r T :=
          ⟨x, lv, si, hvar, hlk, hrootType, hn, hT⟩
        have hnonref : T.isRefLike = false := by rw [hT]; exact hn
        have hsource := h.storage r T hstorage' old hroot
        have hsourceTy : LocTy s.store ⟨r, []⟩ lv.ty := by simpa [hT] using hsource
        obtain ⟨oldValue, hrootOld, htypeOld⟩ := LocTy.hasTyRoot hsource hnonref
        obtain ⟨newValue, hrootNew, htypeNew⟩ :=
          hstorageTypes r T hstorage' oldValue hrootOld htypeOld
        have hnotUnit : T ≠ .unit := by
          intro heq
          have heq' : lv.ty = .unit := by simpa [hT] using heq
          rw [heq'] at hsourceTy
          rcases hsourceTy with ⟨_, _, hflat⟩
          simp [FlatTy] at hflat
        have hnotTuple : ∀ fields, T ≠ .tuple fields := by
          intro fields heq
          have heq' : lv.ty = .tuple fields := by simpa [hT] using heq
          rw [heq'] at hsourceTy
          rcases hsourceTy with ⟨_, _, hflat⟩
          simp [FlatTy] at hflat
        have hflatNew : FlatTy T newValue := by
          cases T with
          | int _ => exact htypeNew
          | bool => exact htypeNew
          | unit => exact False.elim (hnotUnit rfl)
          | arr _ _ => exact htypeNew
          | grow _ => exact htypeNew
          | growshrink _ => exact htypeNew
          | limited _ _ => exact htypeNew
          | ref _ _ => simp [Ty.isRefLike] at hnonref
          | slice _ _ => simp [Ty.isRefLike] at hnonref
          | tuple fields => exact False.elim (hnotTuple fields rfl)
          | structT _ _ => exact htypeNew
        exact ⟨newValue, (read_ok_iff _ _ _).2 ⟨newValue, hrootNew, get_nil _⟩, hflatNew⟩
    rooted := by
      intro x lv si v h1 h2 h3 r htarget
      by_cases hd : ∃ E, D' (RootInst.local env.act si x) E
      · obtain ⟨E, hd⟩ := hd
        obtain ⟨v', g1, _, g3⟩ := hsa _ E hd
        rw [h3] at g1
        cases g1
        rcases hD _ E hd with ⟨k, _⟩ | ⟨x', lv', si', mu, k1, k2, k3, k4, k5⟩
        · exact absurd k (hfr h2)
        · cases k3
          exact k5 r (g3 r htarget)
      · exact h.rooted x lv si v h1 h2 (he.back _ v h3 htarget.isRef (by simp) hd) r htarget
    inv := hi
    sa := by
      intro r E hd
      obtain ⟨v', g1, g2, g3⟩ := hsa r E (hDall r E hd)
      refine ⟨v', g1, g2, fun t htarget => ?_⟩
      rcases hD r E (hDall r E hd) with ⟨_, k⟩ | ⟨x', lv', si', mu, k1, k2, k3, _⟩
      · exact k t (g3 t htarget)
      · subst k3
        exact absurd hd (hfr k2) }

/-- Replacing the slice a caller's slice variable holds, through a reference
to it: the frame holds, and the code around sees only that variable change. -/
theorem Frame.outwrite {future : List VarId} (h : Frame m W tenv penv env s future)
    {r : RootInst} {E : Ty} {w : Val}
    (hd : W.D r E) (hw : HasTy m W.G s.store w (.slice .mutable E))
    (ht : ∀ t, Targets w t → W.A r t) :
    Frame m W tenv penv env { s with store := ⟨(s.store.roots.erase r).insert r w⟩ } future ∧
    Ext (insts env) (Dset W) s { s with store := ⟨(s.store.roots.erase r).insert r w⟩ } := by
  obtain ⟨old, ho, hot, _⟩ := h.sa r E hd
  have hold : IsRef old := by obtain ⟨l, a, b, rfl, _⟩ := hot; trivial
  have hle := rebind_le s.store r old w ho hold
  have hne : ∀ {x : VarId} {sc si : Nat}, env.scopes.lookup sc = some si →
      ¬ (r = RootInst.local env.act si x) := by
    intro x sc si hl e
    obtain ⟨a, si', x', e', hlt⟩ := h.dOut r E hd
    rw [e] at e'
    cases e'
    exact absurd (h.inst_lt hl).1 (Nat.not_le.2 hlt)
  refine ⟨?_, ?_⟩
  · exact
    { h with
      below := h.below, base_le := h.base_le
      vis := by
        intro x hvisible hfuture
        obtain ⟨lv, si, v, h1, h2, h3, h4, h5⟩ := h.vis x hvisible hfuture
        exact ⟨lv, si, v, h1, h2, h3, by simp [get_reinsert, hne h2, h4], h5.mono hle⟩
      bindings := by
        intro x hx
        obtain ⟨lv, si, v, hvar, hlk, hparam, hroot, hshape⟩ := h.bindings x hx
        have hnot := hne (x := x) (sc := lv.scope) (si := si) hlk
        refine ⟨lv, si, v, hvar, hlk, hparam, ?_, hshape⟩
        simp [get_reinsert, hnot, hroot]
      rooted := by
        intro x lv si v h1 h2 h3 t ht'
        simp only [get_reinsert, hne h2, if_false] at h3
        exact h.rooted x lv si v h1 h2 h3 t ht'
      storage := by
        intro r' T hstorage v' hpost
        rcases hstorage with ⟨x, lv, si', hvar, hlk, rfl, hnonref, rfl⟩
        have hnot : ¬ (r = RootInst.local env.act si' x) := hne hlk
        have hpre : s.store.roots[RootInst.local env.act si' x]? = some v' := by
          rw [get_reinsert] at hpost
          simpa [hnot] using hpost
        have hstorage' : StorageRootTypes env (RootInst.local env.act si' x) lv.ty :=
          ⟨x, lv, si', hvar, hlk, rfl, hnonref, rfl⟩
        exact LocTy.mono hle (h.storage _ _ hstorage' v' hpre)
      inv := h.inv.rebind ho hold hw.held (fun t ht' => h.aOlder r t (ht t ht'))
      sa := by
        intro r' E' hd'
        by_cases e : r = r'
        · subst e
          have := h.dFun r E E' hd hd'
          subst this
          exact ⟨w, by simp [get_reinsert], hw.mono hle, ht⟩
        · obtain ⟨v0, h1, h2, h3⟩ := h.sa r' E' hd'
          exact ⟨v0, by simp [get_reinsert, e, h1], h2.mono hle, h3⟩ }
  · refine ⟨hle, Nat.le_refl _, ?_, ?_, ?_⟩
    · intro r0 v hv _ _ hnd
      have e : ¬ (r = r0) := by rintro rfl; exact hnd ⟨E, hd⟩
      simp [get_reinsert, e, hv]
    · intro r0 v hv _ _ hnd
      have e : ¬ (r = r0) := by rintro rfl; exact hnd ⟨E, hd⟩
      simpa [get_reinsert, e] using hv
    · intro r0 hr
      by_cases e : r = r0
      · subst e; simp [ho]
      · simpa [get_reinsert, e] using hr

/-- Entering a block: a scope instance no root has yet. -/
theorem Frame.push {future : List VarId} (h : Frame m W tenv penv env s future)
    {sc : Nat} (hsc : sc ∉ tenv.scopes) :
    Frame m W { tenv with scopes := sc :: tenv.scopes } { penv with scopes := sc :: penv.scopes }
      { env with scopes := (sc, s.nextScope) :: env.scopes }
      { s with nextScope := s.nextScope + 1 } future := by
  have hsc' : sc ∉ env.scopes.map Prod.fst := h.scopes_t ▸ hsc
  have hlk : ∀ a b, env.scopes.lookup a = some b →
      ((sc, s.nextScope) :: env.scopes).lookup a = some b := by
    intro a b hab
    rw [lookup_cons]
    have : a ≠ sc := fun e => hsc' (e ▸ lookup_key hab)
    simp [this, hab]
  have hgam : ∀ rho r, Gam env W.P rho r →
      Gam { env with scopes := (sc, s.nextScope) :: env.scopes } W.P rho r := by
    rintro rho r ⟨q, hq, hr⟩
    refine ⟨q, hq, ?_⟩
    cases q with
    | «local» y =>
      obtain ⟨lv, si, h1, h2, h3⟩ := hr
      exact ⟨lv, si, h1, hlk _ _ h2, h3⟩
    | global g => exact hr
    | param j => exact hr
  have hInvOld : StoreInvAt m W.G { env with scopes := (sc, s.nextScope) :: env.scopes }
      tenv.visible future s := by
    apply h.inv.changeDemand
    intro r hdem
    cases r with
    | global g => exact Or.inl trivial
    | «local» a si x =>
      rcases hdem with ⟨ha, hx, hf, lv, hvar, hlk'⟩
      have hvar' : env.vars[x]? = some lv := hvar
      by_cases hsc' : lv.scope = sc
      · rw [lookup_cons, hsc'] at hlk'
        simp at hlk'
        subst si
        have hnone : s.store.roots[RootInst.local env.act s.nextScope x]? = none := by
          cases hr : s.store.roots[RootInst.local env.act s.nextScope x]? with
          | none => rfl
          | some v =>
            have hlt := h.inv.fresh env.act s.nextScope x (by rw [hr]; simp)
            exact absurd hlt (Nat.not_lt.mpr (Nat.le_refl _))
        rw [ha]
        exact Or.inr hnone
      · have hlk : env.scopes.lookup lv.scope = some si := by
          rw [lookup_cons, if_neg hsc'] at hlk'
          exact hlk'
        exact Or.inl ⟨ha, hx, hf, lv, hvar', hlk⟩
  have hInv : StoreInvAt m W.G { env with scopes := (sc, s.nextScope) :: env.scopes }
      tenv.visible future { s with nextScope := s.nextScope + 1 } := by
    refine ⟨hInvOld.live, hInvOld.age, ?_, hInvOld.globals⟩
    intro a si x hx
    exact Nat.lt_succ_of_lt (hInvOld.fresh a si x hx)
  exact
  { mod_t := h.mod_t, mod_p := h.mod_p, vars_t := h.vars_t, vars_p := h.vars_p
    scopes_t := by simp [h.scopes_t]
    scopes_p := by simp [h.scopes_p]
    nodup := by
      simp only [List.map_cons]
      exact List.nodup_cons.2 ⟨hsc', h.nodup⟩
    sorted := by
      refine List.pairwise_cons.2 ⟨fun p hp => (h.below p hp).2, h.sorted⟩
    below := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨h.base_le, Nat.lt_succ_self _⟩
      · exact ⟨(h.below p hp).1, Nat.lt_succ_of_lt (h.below p hp).2⟩
    base_le := Nat.le_succ_of_le h.base_le
    pAge := h.pAge
    vis := by
      intro x hx
      intro hfut
      obtain ⟨lv, si, v, h1, h2, h3, h4, h5⟩ := h.vis x hx hfut
      exact ⟨lv, si, v, h1, hlk _ _ h2, h3, h4, h5⟩
    bindings := by
      intro x hx
      obtain ⟨lv, si, v, hvar, hlookup, hparam, hroot, hshape⟩ := h.bindings x hx
      exact ⟨lv, si, v, hvar, hlk _ _ hlookup, hparam, hroot, hshape⟩
    storage := by
      intro r T hstorage v hroot
      rcases hstorage with ⟨x, lv, si, hvar, hlookup, rfl, hnonref, rfl⟩
      rw [lookup_cons] at hlookup
      by_cases hscope : lv.scope = sc
      · simp only [hscope, if_pos, Option.some.injEq] at hlookup
        have hnone : s.store.roots[RootInst.local env.act s.nextScope x]? = none := by
          cases hr : s.store.roots[RootInst.local env.act s.nextScope x]? with
          | none => rfl
          | some old =>
            have hlt := h.inv.fresh env.act s.nextScope x (by rw [hr]; simp)
            exact False.elim (Nat.not_lt.mpr (Nat.le_refl _) hlt)
        have hroot' : s.store.roots[RootInst.local env.act s.nextScope x]? = some v := by
          simpa [hlookup] using hroot
        rw [hroot'] at hnone
        cases hnone
      · simp only [hscope, if_neg] at hlookup
        have hstorageOld : StorageRootTypes env (RootInst.local env.act si x) lv.ty :=
          ⟨x, lv, si, hvar, hlookup, rfl, hnonref, rfl⟩
        exact h.storage _ _ hstorageOld v hroot
    rooted := by
      intro x lv si v h1 h2 h3 r ht
      have h2' : ((sc, s.nextScope) :: env.scopes).lookup lv.scope = some si := h2
      rw [lookup_cons] at h2'
      by_cases e : lv.scope = sc
      · simp only [e, if_true, Option.some.injEq] at h2'
        subst h2'
        exact absurd (h.inv.fresh _ _ _ (by rw [h3]; simp)) (Nat.lt_irrefl _)
      · simp only [e, if_false] at h2'
        obtain ⟨ann, ha, hg⟩ := h.rooted x lv si v h1 h2' h3 r ht
        exact ⟨ann, ha, hgam _ _ hg⟩
    inv := hInv
    aOlder := h.aOlder, dOut := h.dOut, dFun := h.dFun, sa := h.sa, pref := h.pref }

/-! ### Leaving a block -/

/-- The state after the roots of block `sc`, instance `si`, are released. -/
def relSt (env : Env) (sc : Nat) (si : ScopeInst) (s : St) : St :=
  { s with store := releaseVars env.vars env.act sc si env.vars.size s.store }

/-- Releasing a block removes only its newly opened roots from the statement
footprint. The outer frame supplies freshness for the block's scope instance. -/
theorem FootprintS.releaseBlock {future : List VarId} {sc : Nat} {D : RootInst → Prop}
    {s2 : St} (hframe : Frame m W tenv penv env s future)
    (h : FootprintS { env with scopes := (sc, s.nextScope) :: env.scopes } D
      { s with nextScope := s.nextScope + 1 } s2) :
    Footprint (insts env) D s (relSt env sc s.nextScope s2) := by
  let inner := { env with scopes := (sc, s.nextScope) :: env.scopes }
  have hinsts : insts inner = s.nextScope :: insts env := by simp [insts, inner]
  have hcurrent : ∀ a x, s.store.roots[RootInst.local a s.nextScope x]? = none := by
    intro a x
    cases hroot : s.store.roots[RootInst.local a s.nextScope x]? with
    | none => rfl
    | some v =>
      have hlt : s.nextScope < s.nextScope :=
        hframe.inv.fresh a s.nextScope x (by rw [hroot]; simp)
      exact False.elim ((Nat.lt_irrefl _) hlt)
  have htop : ∀ r, TopRoot inner r → ScopeRoots env.vars env.act sc s.nextScope r := by
    intro r hroot
    rcases hroot with ⟨x, lv, si, rest, hscopes, hvar, hr⟩
    dsimp only [inner] at hscopes hr hvar
    simp only [List.cons.injEq, Prod.mk.injEq] at hscopes
    rcases hscopes with ⟨⟨hscope, hsi⟩, _⟩
    subst si
    subst r
    exact ⟨x, lv, hvar, hscope.symm, rfl⟩
  have hnotInner : ∀ r, s.store.roots[r]? ≠ none →
      (∀ a si x, r = RootInst.local a si x → si ∉ insts env) →
      ∀ a si x, r = RootInst.local a si x → si ∉ insts inner := by
    intro r hr hn a si x heq hmem
    by_cases hcurrentScope : si = s.nextScope
    · have hroot : s.store.roots[RootInst.local a si x]? ≠ none := by
        rw [← heq]
        exact hr
      have hroot' : s.store.roots[RootInst.local a s.nextScope x]? ≠ none := by
        simpa [hcurrentScope] using hroot
      exact hroot' (hcurrent a x)
    · have htail : si ∈ insts env := by
        have hmem' : si ∈ s.nextScope :: insts env := by simpa [hinsts] using hmem
        exact (List.mem_cons.1 hmem').resolve_left hcurrentScope
      exact hn a si x heq htail
  obtain ⟨hagree, hgone⟩ := releaseScope_roots env.vars env.act sc s.nextScope s2.store
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Nat.le_trans (Nat.le_succ _) h.next
  · intro r v hv hr hn hd
    have hnotScope : ¬ ScopeRoots env.vars env.act sc s.nextScope r := by
      intro hp
      rcases hp with ⟨x, lv, hvar, hscope, rfl⟩
      have hnone := hcurrent env.act x
      rw [hv] at hnone
      cases hnone
    have hkeep := h.keep r v hv hr (hnotInner r (by rw [hv]; simp) hn) hd
    show (releaseVars env.vars env.act sc s.nextScope env.vars.size s2.store).roots[r]? = some v
    rw [hagree r hnotScope]
    exact hkeep
  · intro r v hv hr hn hd
    have hnotScope : ¬ ScopeRoots env.vars env.act sc s.nextScope r := by
      intro hp
      change (releaseVars env.vars env.act sc s.nextScope env.vars.size s2.store).roots[r]? = some v at hv
      rw [hgone r hp] at hv
      cases hv
    have hpost : s2.store.roots[r]? = some v := by
      change (releaseVars env.vars env.act sc s.nextScope env.vars.size s2.store).roots[r]? = some v at hv
      rw [hagree r hnotScope] at hv
      exact hv
    have hnotInner : ∀ a si x, r = RootInst.local a si x → si ∉ insts inner := by
      intro a si x heq hmem
      by_cases hcurrentScope : si = s.nextScope
      · have hsource : s.store.roots[r]? ≠ none := by
          rcases h.dom r (by rw [hpost]; simp) with hsource | htop'
          · exact hsource
          · exact False.elim (hnotScope (htop r htop'))
        have hsource' : s.store.roots[RootInst.local a si x]? ≠ none := by
          rw [← heq]
          exact hsource
        have hsource'' : s.store.roots[RootInst.local a s.nextScope x]? ≠ none := by
          simpa [hcurrentScope] using hsource'
        exact hsource'' (hcurrent a x)
      · have htail : si ∈ insts env := by
          have hmem' : si ∈ s.nextScope :: insts env := by simpa [hinsts] using hmem
          exact (List.mem_cons.1 hmem').resolve_left hcurrentScope
        exact hn a si x heq htail
    have hback := h.back r v hpost hr hnotInner hd
    exact hback
  · intro r hr
    by_cases hp : ScopeRoots env.vars env.act sc s.nextScope r
    · change (releaseVars env.vars env.act sc s.nextScope env.vars.size s2.store).roots[r]? ≠ none at hr
      exact False.elim (hr (hgone r hp))
    · have hpost : s2.store.roots[r]? ≠ none := by
        change (releaseVars env.vars env.act sc s.nextScope env.vars.size s2.store).roots[r]? ≠ none at hr
        rw [← hagree r hp]
        exact hr
      rcases h.dom r hpost with hsource | htop'
      · exact hsource
      · exact False.elim (hp (htop r htop'))

/-- The pilot store-growth contract survives releasing roots newer than the
source frame. This is separate from the profile-independent footprint proof. -/
theorem PilotStoreLe.releaseScope {future : List VarId} {sc : Nat} {si : ScopeInst}
    {s2 : St} (hframe : Frame m W tenv penv env s future)
    (hsi : s.nextScope ≤ si) (hle : PilotStoreLe m s s2) :
    PilotStoreLe m s (relSt env sc si s2) := by
  intro hp
  obtain ⟨hagree, _⟩ := releaseScope_roots env.vars env.act sc si s2.store
  have hfresh : ∀ r, ScopeRoots env.vars env.act sc si r → s.store.roots[r]? = none := by
    rintro r ⟨x, lv, hvar, hscope, rfl⟩
    cases hroot : s.store.roots[RootInst.local env.act si x]? with
    | none => rfl
    | some v =>
      have hlt : si < s.nextScope := hframe.inv.fresh env.act si x (by rw [hroot]; simp)
      exact False.elim ((Nat.not_lt_of_ge hsi) hlt)
  apply storeLe_release (P := ScopeRoots env.vars env.act sc si) (hle hp)
  · intro r hnot
    change (releaseVars env.vars env.act sc si env.vars.size s2.store).roots[r]? = s2.store.roots[r]?
    exact hagree r hnot
  · exact hfresh

section Agree
variable {G : Nat} {st st' : Store} {P : RootInst → Prop}

theorem SliceTy.agree {l : Loc} {a n : Nat} {E : Ty}
    (hagree : ∀ r, ¬ P r → st'.roots[r]? = st.roots[r]?) (hl : ¬ P l.root)
    (h : SliceTy st l a n E) : SliceTy st' l a n E := by
  obtain ⟨v, es, h1, h2, h3, h4⟩ := h
  exact ⟨v, es, read_agree hagree hl h1, h2, h3, h4⟩

theorem LocOk.agree {l : Loc} {T : Ty}
    (hagree : ∀ r, ¬ P r → st'.roots[r]? = st.roots[r]?) (hl : ¬ P l.root)
    (h : LocOk m G st l T) : LocOk m G st' l T :=
  h.elim (fun h => Or.inl (locTy_agree hagree hl h)) Or.inr

theorem HasTy.agree {v : Val} {T : Ty}
    (hagree : ∀ r, ¬ P r → st'.roots[r]? = st.roots[r]?) (ht : ∀ r, Targets v r → ¬ P r)
    (h : HasTy m G st v T) : HasTy m G st' v T := by
  cases T <;> simp only [HasTy] at h ⊢ <;> try exact h
  · obtain ⟨l, rfl, h2⟩ := h
    refine ⟨l, rfl, h2.elim (fun h => Or.inl ⟨h.1, h.2.1.agree hagree (ht _ rfl), h.2.2⟩)
      (fun h => Or.inr ⟨h.1, h.2.1, ?_⟩)⟩
    rw [hagree _ (ht _ rfl)]; exact h.2.2
  · obtain ⟨l, a, n, rfl, h2, h3⟩ := h
    exact ⟨l, a, n, rfl, h2, h3.agree hagree (ht _ rfl)⟩

theorem Held.agree {v : Val}
    (hagree : ∀ r, ¬ P r → st'.roots[r]? = st.roots[r]?) (ht : ∀ r, Targets v r → ¬ P r)
    (h : Held m G st v) : Held m G st' v := by
  cases v <;> simp only [Held] at h ⊢
  · refine h.elim (fun ⟨T, h2, h3⟩ => Or.inl ⟨T, h2, h3.agree hagree (ht _ rfl)⟩)
      (fun h => Or.inr ⟨h.1, ?_⟩)
    rw [hagree _ (ht _ rfl)]; exact h.2
  · obtain ⟨E, h3⟩ := h
    exact ⟨E, h3.agree hagree (ht _ rfl)⟩

/-- A typed value remains typed after scope release when it does not target
any root released with that scope. -/
theorem HasTy.releaseScope {G : Nat} {s2 : St} {sc : Nat} {si : ScopeInst}
    {v : Val} {T : Ty} (h : HasTy m G s2.store v T)
    (hsurv : ∀ r, Targets v r → ¬ ScopeRoots env.vars env.act sc si r) :
    HasTy m G (relSt env sc si s2).store v T := by
  obtain ⟨hagree, _⟩ := releaseScope_roots env.vars env.act sc si s2.store
  apply h.agree
  · intro r hnot
    change (releaseVars env.vars env.act sc si env.vars.size s2.store).roots[r]? = s2.store.roots[r]?
    exact hagree r hnot
  · exact hsurv

/-- An older holder's stored references cannot target a younger scope. -/
private theorem BeforeBase.older_target {base : Nat} {holder target : RootInst}
    (hholder : BeforeBase base holder) (hage : Older target holder) : BeforeBase base target := by
  cases holder with
  | global g =>
    cases target with
    | global g' => trivial
    | «local» a si x => exact False.elim (by simpa [Older] using hage)
  | «local» a si x =>
    cases target with
    | global g => trivial
    | «local» a' si' x' =>
      have hsi : si < base := by simpa [BeforeBase] using hholder
      have hsi' : si' ≤ si := by simpa [Older] using hage
      exact Nat.lt_of_le_of_lt hsi' hsi

/-- Caller observations survive release of a scope at or after their
activation base. The frame age invariant excludes released roots from every
observed value. -/
theorem ObservedSafe.releaseScope {future : List VarId} {sc : Nat} {si : ScopeInst}
    {shrinking : RootInst → Prop} {o : Observation} {s2 : St}
    (h : ObservedSafe m W shrinking o s2.store)
    (hframe : Frame m W tenv penv env s2 future) (hbase : W.base ≤ si) :
    ObservedSafe m W shrinking o (relSt env sc si s2).store := by
  obtain ⟨hagree, _⟩ := releaseScope_roots env.vars env.act sc si s2.store
  have before_notScope : ∀ r, BeforeBase W.base r → ¬ ScopeRoots env.vars env.act sc si r := by
    intro r hbefore hp
    rcases hp with ⟨x, lv, hvar, hscope, rfl⟩
    change si < W.base at hbefore
    exact (Nat.not_lt_of_ge hbase) hbefore
  have roots_notScope : ∀ r T, o.roots r T → ∀ v, s2.store.roots[r]? = some v →
      ∀ target, Targets v target → ¬ ScopeRoots env.vars env.act sc si target := by
    intro r T hobs v hv target htarget hscope
    exact before_notScope target
      (BeforeBase.older_target (h.rootsOlder r T hobs) (hframe.inv.age r v hv target htarget)) hscope
  have values_notScope : ∀ v T, o.values v T → ∀ target, Targets v target →
      ¬ ScopeRoots env.vars env.act sc si target := by
    intro v T hobs target htarget
    exact before_notScope target (h.valuesOlder v T hobs target htarget)
  refine ⟨?_, h.rootsOlder, h.valuesOlder, ?_, h.valuesProtected⟩
  · constructor
    · intro r T hobs
      obtain ⟨v, hv, hty⟩ := h.typed.roots r T hobs
      have hnot := before_notScope r (h.rootsOlder r T hobs)
      have hnew : (relSt env sc si s2).store.roots[r]? = some v := by
        change (releaseVars env.vars env.act sc si env.vars.size s2.store).roots[r]? = some v
        rw [hagree r hnot]
        exact hv
      exact ⟨v, hnew, hty.releaseScope (roots_notScope r T hobs v hv)⟩
    · intro v T hobs
      exact (h.typed.values v T hobs).releaseScope (values_notScope v T hobs)
  · intro r T v hobs hv hinterior target htarget
    have hnot := before_notScope r (h.rootsOlder r T hobs)
    have hv0 : s2.store.roots[r]? = some v := by
      change (releaseVars env.vars env.act sc si env.vars.size s2.store).roots[r]? = some v at hv
      rw [hagree r hnot] at hv
      exact hv
    exact h.rootsProtected r T v hobs hv0 hinterior target htarget

/-- Aliases rooted in the caller's frame keep their runtime typing when a
younger scope is released. Their static roots still denote the same roots. -/
theorem RetainsAliases.releaseScope {future : List VarId} {sc : Nat} {si : ScopeInst}
    {s2 : St} {aliases : List RetainedAlias}
    (hframe : Frame m W tenv penv env s future) (hsi : s.nextScope ≤ si) :
    RetainsAliases m W env s2.store (relSt env sc si s2).store aliases := by
  intro alias hmem v ⟨hty, hroots⟩
  refine ⟨hty.releaseScope (env := env) ?_, hroots⟩
  intro r htarget hscope
  rcases hscope with ⟨x, lv, hvar, hdecl, rfl⟩
  have hbefore := hframe.gam_older (hroots _ htarget) env.act si x rfl
  exact (Nat.not_lt_of_ge hsi) hbefore

/-- Releasing roots no surviving reference targets keeps the store invariant. -/
theorem StoreInv.release {s : St} {demanded : RootInst → Prop} (hi : StoreInv m G s demanded)
    (hagree : ∀ r, ¬ P r → st'.roots[r]? = s.store.roots[r]?)
    (hgone : ∀ r, P r → st'.roots[r]? = none)
    (hsurv : ∀ (r : RootInst) (v : Val), ¬ P r → s.store.roots[r]? = some v →
      ∀ r', Targets v r' → ¬ P r')
    (hglob : ∀ g, ¬ P (.global g)) : StoreInv m G { s with store := st' } demanded := by
  have back : ∀ (r : RootInst) (v : Val), st'.roots[r]? = some v →
      ¬ P r ∧ s.store.roots[r]? = some v := by
    intro r v hv
    by_cases hp : P r
    · rw [hgone r hp] at hv; cases hv
    · exact ⟨hp, by rw [← hagree r hp]; exact hv⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r v hv hdem
    obtain ⟨hp, h0⟩ := back r v hv
    exact (hi.live r v h0 hdem).agree hagree (hsurv r v hp h0)
  · intro r v hv
    exact hi.age r v (back r v hv).2
  · intro a si x hx
    cases hv : st'.roots[RootInst.local a si x]? with
    | none => exact absurd hv hx
    | some v => exact hi.fresh a si x (by rw [(back _ v hv).2]; simp)
  · intro g gl hg hgl
    exact locTy_agree hagree (hglob g) (hi.globals g gl hg hgl)

end Agree

/-- A root that is not of the released scope instance and holds a reference
points outside that instance, when every other root is older than it. -/
theorem survivor_targets {G : Nat} {s2 : St} {sc : Nat} {si : ScopeInst}
    {demanded : RootInst → Prop} (hi : StoreInv m G s2 demanded)
    (hdom : ∀ (r : RootInst), s2.store.roots[r]? ≠ none →
      ScopeRoots env.vars env.act sc si r ∨ ∀ a si' x, r = RootInst.local a si' x → si' < si)
    (r : RootInst) (v : Val) (hp : ¬ ScopeRoots env.vars env.act sc si r)
    (hv : s2.store.roots[r]? = some v) (r' : RootInst) (ht : Targets v r') :
    ¬ ScopeRoots env.vars env.act sc si r' := by
  rintro ⟨x, lv, _, _, rfl⟩
  have hold := hi.age r v hv _ ht
  rcases hdom r (by rw [hv]; simp) with h | h
  · exact hp h
  · cases r with
    | global g => exact hold
    | «local» a si' x' =>
      have h2 : si' < si := h a si' x' rfl
      have h1 : si ≤ si' := hold
      exact absurd h1 (Nat.not_le.2 h2)

/-- Leaving a block: the frame of the code around it holds once the block's
roots are released, given that every other root is older than the block. -/
theorem Frame.pop {future future' : List VarId} {tenv1 : TEnv} {s2 : St} {sc : Nat} {si : ScopeInst}
    (h : Frame m W tenv1 { penv with scopes := sc :: penv.scopes }
      { env with scopes := (sc, si) :: env.scopes } s2 future)
    (hmod : tenv.mod = tenv1.mod) (hvars : tenv.vars = tenv1.vars)
    (hscs : tenv1.scopes = sc :: tenv.scopes)
    (hvis : ∀ x, x ∈ tenv.visible → x ∈ tenv1.visible ∧
      ∃ lv, env.vars[x]? = some lv ∧ lv.scope ∈ env.scopes.map Prod.fst)
    (hfuture : ∀ x, x ∈ future' → x ∈ future)
    (hdom : ∀ (r : RootInst), s2.store.roots[r]? ≠ none →
      ScopeRoots env.vars env.act sc si r ∨ ∀ a si' x, r = RootInst.local a si' x → si' < si) :
    Frame m W tenv penv env (relSt env sc si s2) future' := by
  obtain ⟨hagree, hgone⟩ := releaseScope_roots env.vars env.act sc si s2.store
  have K := survivor_targets (env := env) h.inv hdom
  have hnd : sc ∉ env.scopes.map Prod.fst ∧ (env.scopes.map Prod.fst).Nodup := by
    have := h.nodup
    simpa [List.nodup_cons] using this
  obtain ⟨hhd, htl⟩ := List.pairwise_cons.1 h.sorted
  have hlk : ∀ a b, env.scopes.lookup a = some b →
      ((sc, si) :: env.scopes).lookup a = some b ∧
      ∀ x, ¬ ScopeRoots env.vars env.act sc si (.local env.act b x) := by
    intro a b hab
    refine ⟨?_, ?_⟩
    · rw [lookup_cons]
      have : a ≠ sc := fun e => hnd.1 (e ▸ lookup_key hab)
      simp [this, hab]
    · rintro x ⟨x', lv', _, _, e⟩
      cases e
      have := hhd _ (lookup_mem _ _ _ hab)
      simp at this
  have st2 : tenv.scopes = env.scopes.map Prod.fst := by
    have := h.scopes_t
    rw [hscs] at this
    simpa using this
  have sp2 : penv.scopes = env.scopes.map Prod.fst := by
    have := h.scopes_p
    simpa using this
  have hInvReleased : StoreInv m W.G (relSt env sc si s2)
      (DemandedRoot { env with scopes := (sc, si) :: env.scopes } tenv1.visible future) :=
    h.inv.release hagree hgone K (by rintro g ⟨_, _, _, _, e⟩; cases e)
  have hInv : StoreInvAt m W.G env tenv.visible future' (relSt env sc si s2) := by
    apply hInvReleased.changeDemand
    intro r hdem
    cases r with
    | global g => exact Or.inl trivial
    | «local» a si' x =>
      rcases hdem with ⟨ha, hx, hf, lv, hvar, hlk⟩
      obtain ⟨hx1, lv0, hlv0, hsc0⟩ := hvis x hx
      have hvar' : env.vars[x]? = some lv := by
        simpa using hvar
      have hlvEq : lv = lv0 := Option.some.inj (hvar'.symm.trans hlv0)
      subst lv0
      have hscNe : lv.scope ≠ sc := fun heq => hnd.1 (heq ▸ hsc0)
      have hlookupInner : ((sc, si) :: env.scopes).lookup lv.scope = some si' := by
        rw [lookup_cons]
        simpa [hscNe] using hlk
      exact Or.inl ⟨ha, hx1, hfuture x hf, lv, hvar', hlookupInner⟩
  exact
  { mod_t := hmod ▸ h.mod_t, mod_p := h.mod_p, vars_t := hvars ▸ h.vars_t, vars_p := h.vars_p
    scopes_t := st2, scopes_p := sp2, nodup := hnd.2, sorted := htl
    below := fun p hp => h.below p (List.mem_cons_of_mem _ hp)
    base_le := h.base_le, pAge := h.pAge
    vis := by
      intro x hx
      intro hfut
      obtain ⟨hx1, lv0, hlv0, hsc0⟩ := hvis x hx
      obtain ⟨lv, si', v, h1, h2, h3, h4, h5⟩ := h.vis x hx1 (hfuture x hfut)
      have h1' : env.vars[x]? = some lv := h1
      rw [hlv0] at h1'; cases h1'
      have hne : lv0.scope ≠ sc := fun e => hnd.1 (e ▸ hsc0)
      have h2' : ((sc, si) :: env.scopes).lookup lv0.scope = some si' := h2
      rw [lookup_cons] at h2'
      simp only [hne, if_false] at h2'
      have hnp := (hlk _ _ h2').2 x
      refine ⟨lv0, si', v, hlv0, h2', h3, ?_, ?_⟩
      · show (releaseVars env.vars env.act sc si env.vars.size s2.store).roots[_]? = some v
        rw [hagree _ hnp]; exact h4
      · exact h5.agree hagree (K _ v hnp h4)
    bindings := by
      intro x hx
      obtain ⟨hx1, lv0, hlv0, hsc0⟩ := hvis x hx
      obtain ⟨lv, si', v, h1, h2, h3, h4, h5⟩ := h.bindings x hx1
      have h1' : env.vars[x]? = some lv := by simpa using h1
      rw [hlv0] at h1'
      cases h1'
      have hne : lv0.scope ≠ sc := fun heq => hnd.1 (heq ▸ hsc0)
      have h2' : ((sc, si) :: env.scopes).lookup lv0.scope = some si' := h2
      rw [lookup_cons] at h2'
      simp only [hne, if_false] at h2'
      have hnp := (hlk _ _ h2').2 x
      refine ⟨lv0, si', v, hlv0, h2', h3, ?_, h5⟩
      show (releaseVars env.vars env.act sc si env.vars.size s2.store).roots[RootInst.local env.act si' x]? = some v
      rw [hagree _ hnp]
      exact h4
    storage := by
      intro r T hstorage v hpost
      rcases hstorage with ⟨x, lv, si', hvar, hlookup, rfl, hnonref, rfl⟩
      have hmemPair := lookup_mem _ _ _ hlookup
      have hmem : lv.scope ∈ env.scopes.map Prod.fst :=
        List.mem_map.mpr ⟨(lv.scope, si'), hmemPair, rfl⟩
      have hscopeNe : lv.scope ≠ sc := by
        intro heq
        apply hnd.1
        simpa [heq] using hmem
      have hnp : ¬ ScopeRoots env.vars env.act sc si (.local env.act si' x) := by
        intro hscope
        obtain ⟨x', lv', hvar', hsc', hroot⟩ := hscope
        have hids : True ∧ si' = si ∧ x = x' := by
          simp only [RootInst.local.injEq] at hroot
          exact hroot
        rcases hids with ⟨_, _, hx⟩
        subst x'
        have hlv : lv' = lv := Option.some.inj (hvar'.symm.trans hvar)
        subst lv'
        exact hscopeNe hsc'
      have hstorageInner :
          StorageRootTypes { env with scopes := (sc, si) :: env.scopes }
            (.local env.act si' x) lv.ty :=
        ⟨x, lv, si', hvar, (hlk _ _ hlookup).1, rfl, hnonref, rfl⟩
      have hpre : s2.store.roots[RootInst.local env.act si' x]? = some v := by
        rw [← hagree _ hnp]
        exact hpost
      obtain ⟨stored, hread, hflat⟩ := h.storage _ _ hstorageInner v hpre
      have hreadValue : s2.store.read ⟨RootInst.local env.act si' x, []⟩ = .ok v :=
        (read_ok_iff _ _ _).2 ⟨v, hpre, get_nil v⟩
      have hstored : stored = v := by
        rw [hreadValue] at hread
        cases hread
        rfl
      rw [hstored] at hflat
      exact ⟨v, (read_ok_iff _ _ _).2 ⟨v, hpost, get_nil v⟩, hflat⟩
    rooted := by
      intro x lv si' v h1 h2 h3 r ht
      have hnp := (hlk _ _ h2).2 x
      have h3' : s2.store.roots[RootInst.local env.act si' x]? = some v := by
        rw [← hagree _ hnp]; exact h3
      obtain ⟨ann, ha, q, hq, hr⟩ := h.rooted x lv si' v h1 (hlk _ _ h2).1 h3' r ht
      refine ⟨ann, ha, q, hq, ?_⟩
      cases q with
      | «local» y =>
        obtain ⟨ly, siy, g1, g2, g3⟩ := hr
        have g2' : ((sc, si) :: env.scopes).lookup ly.scope = some siy := g2
        rw [lookup_cons] at g2'
        by_cases e : ly.scope = sc
        · simp only [e, if_true, Option.some.injEq] at g2'
          subst g2'
          exact absurd ⟨y, ly, g1, e, g3⟩ (K _ v hnp h3' r ht)
        · simp only [e, if_false] at g2'
          exact ⟨ly, siy, g1, g2', g3⟩
      | global g => exact hr
      | param j => exact hr
    inv := hInv
    aOlder := h.aOlder, dOut := h.dOut, dFun := h.dFun, pref := h.pref
    sa := by
      intro r E hd
      obtain ⟨v0, h1, h2, h3⟩ := h.sa r E hd
      obtain ⟨a, si', x', e, hlt⟩ := h.dOut r E hd
      have hbase : W.base ≤ si := (h.below (sc, si) List.mem_cons_self).1
      have hnp : ∀ (t : RootInst), (t = r ∨ Older t r) → ¬ ScopeRoots env.vars env.act sc si t := by
        rintro t ht ⟨y, ly, _, _, rfl⟩
        subst e
        rcases ht with ht | ht
        · cases ht; exact absurd hbase (Nat.not_le.2 hlt)
        · have ht' : si ≤ si' := ht
          exact absurd (Nat.le_trans hbase ht') (Nat.not_le.2 hlt)
      refine ⟨v0, ?_, h2.agree hagree (fun t ht => hnp t (Or.inr (h.aOlder r t (h3 t ht)))), h3⟩
      show (releaseVars env.vars env.act sc si env.vars.size s2.store).roots[r]? = some v0
      rw [hagree r (hnp r (Or.inl rfl))]; exact h1 }

/-- Leaving a block, seen from the code around it. -/
theorem ext_block {G : Nat} {s s2 : St} {sc : Nat} {D : RootInst → Prop}
    {demanded : RootInst → Prop} (hi : StoreInv m G s demanded)
    (hle : StoreLe s.store s2.store) (hnext : s.nextScope ≤ s2.nextScope)
    (hkeep : ∀ (r : RootInst) (v : Val), s.store.roots[r]? = some v → IsRef v →
      (∀ a si' x, r = RootInst.local a si' x → si' ∉ insts env) → ¬ D r →
      s2.store.roots[r]? = some v)
    (hback : ∀ (r : RootInst) (v : Val), s2.store.roots[r]? = some v → IsRef v →
      (∀ a si' x, r = RootInst.local a si' x → si' ∉ s.nextScope :: insts env) → ¬ D r →
      s.store.roots[r]? = some v)
    (hdom : ∀ (r : RootInst), s2.store.roots[r]? ≠ none →
      s.store.roots[r]? ≠ none ∨ ScopeRoots env.vars env.act sc s.nextScope r) :
    Ext (insts env) D s (relSt env sc s.nextScope s2) := by
  obtain ⟨hagree, hgone⟩ := releaseScope_roots env.vars env.act sc s.nextScope s2.store
  have hfresh : ∀ r, ScopeRoots env.vars env.act sc s.nextScope r → s.store.roots[r]? = none := by
    rintro r ⟨x, lv, _, _, rfl⟩
    cases hv : s.store.roots[RootInst.local env.act s.nextScope x]? with
    | none => rfl
    | some v => exact absurd (hi.fresh _ _ _ (by rw [hv]; simp)) (Nat.lt_irrefl _)
  have hnp : ∀ (r : RootInst), s.store.roots[r]? ≠ none →
      ¬ ScopeRoots env.vars env.act sc s.nextScope r := fun r hr hp => hr (hfresh r hp)
  refine ⟨storeLe_release _ hle hagree hfresh, hnext, ?_, ?_, ?_⟩
  · intro r v hv hr hn hd
    show (releaseVars env.vars env.act sc s.nextScope env.vars.size s2.store).roots[r]? = some v
    rw [hagree r (hnp r (by rw [hv]; simp))]
    exact hkeep r v hv hr hn hd
  · intro r v hv hr hn hd
    have hv' : (releaseVars env.vars env.act sc s.nextScope env.vars.size s2.store).roots[r]? = some v := hv
    by_cases hp : ScopeRoots env.vars env.act sc s.nextScope r
    · rw [hgone r hp] at hv'; cases hv'
    · rw [hagree r hp] at hv'
      refine hback r v hv' hr ?_ hd
      intro a si' x e hmem
      rcases List.mem_cons.1 hmem with e' | e'
      · subst e; subst e'
        rcases hdom _ (by rw [hv']; simp) with h0 | h0
        · exact absurd (hi.fresh _ _ _ h0) (Nat.lt_irrefl _)
        · exact hp h0
      · exact hn a si' x e e'
  · intro r hr
    have hr' : (releaseVars env.vars env.act sc s.nextScope env.vars.size s2.store).roots[r]? ≠ none := hr
    by_cases hp : ScopeRoots env.vars env.act sc s.nextScope r
    · exact absurd (hgone r hp) hr'
    · rw [hagree r hp] at hr'
      exact (hdom r hr').elim id (fun h => absurd h hp)

end Goose.Core.Sound

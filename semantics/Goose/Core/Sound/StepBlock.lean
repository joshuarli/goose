import Goose.Core.Sound.StepAux

/-!
One step of the induction on fuel for statement lists and blocks: binding the
variables a construct declares, running the body, and releasing the scope.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {plans : Array (Array DemandPoint)} {n : Nat}

theorem m_bind_assoc {α β γ : Type} (x : M α) (f : α → M β) (g : β → M γ) :
    ((x >>= f) >>= g) = x >>= fun a => f a >>= g := by
  funext s
  show M.bind' (M.bind' x f) g s = M.bind' x (fun a => M.bind' (f a) g) s
  unfold M.bind'
  cases x s <;> rfl

theorem m_pure_bind {α β : Type} (a : α) (f : α → M β) : (pure a >>= f) = f a := rfl

theorem sat_release_bind {env : Env} {sc : Nat} {si : ScopeInst} {s : St} {f : Unit → M α}
    {Q : α → St → Prop} :
    Sat (releaseScope env sc si >>= f) s Q ↔ Sat (f ()) (relSt env sc si s) Q := Iff.rfl

/-- The store after the variables of a construct are bound in its block. -/
def preStore (act : ActId) (si : ScopeInst) : List (VarId × Val) → Store → Store
  | [], st => st
  | (x, v) :: rest, st => preStore act si rest (st.introduce (.local act si x) v)

theorem bindAll_eq (act : ActId) (si : ScopeInst) : ∀ (pre : List (VarId × Val)) (s : St),
    bindAll act si pre s = .ok () { s with store := preStore act si pre s.store }
  | [], s => rfl
  | (x, v) :: rest, s => by
    show M.bind' (bindRoot (.local act si x) v) (fun _ => bindAll act si rest) s = _
    simp only [M.bind', bindRoot]
    exact bindAll_eq act si rest _

theorem sat_bindAll_bind {act : ActId} {si : ScopeInst} {pre : List (VarId × Val)} {s : St}
    {f : Unit → M α} {Q : α → St → Prop} :
    Sat (bindAll act si pre >>= f) s Q ↔
      Sat (f ()) { s with store := preStore act si pre s.store } Q := by
  show Sat (M.bind' (bindAll act si pre) f) s Q ↔ _
  unfold Sat M.bind'
  rw [bindAll_eq]

/-- A typed reference or slice points into a root of the store, or at a global. -/
theorem hasTy_target_dom {G : Nat} {st : Store} {v : Val} {T : Ty} {r : RootInst}
    (h : HasTy m G st v T) (hr : Targets v r) : (∃ g, r = .global g) ∨ st.roots[r]? ≠ none := by
  cases T with
  | ref mu T' =>
    obtain ⟨l, rfl, hh⟩ := h
    cases hr
    rcases hh with ⟨_, hl⟩ | ⟨_, _, hlive⟩
    · rcases hl with ⟨x, hx, _⟩ | ⟨g, gl, _, hroot, _⟩
      · obtain ⟨old, ho, _⟩ := (read_ok_iff _ _ _).1 hx
        exact Or.inr (by rw [ho]; simp)
      · exact Or.inl ⟨g, hroot⟩
    · exact Or.inr hlive
  | slice mu E =>
    obtain ⟨l, a, b, rfl, _, x, es, hx, _⟩ := h
    cases hr
    obtain ⟨old, ho, _⟩ := (read_ok_iff _ _ _).1 hx
    exact Or.inr (by rw [ho]; simp)
  | unit => cases h; exact hr.elim
  | tuple ts => exact h.elim
  | int t => exact absurd hr.isRef (flat_not_ref h)
  | bool => exact absurd hr.isRef (flat_not_ref h)
  | arr E k => exact absurd hr.isRef (flat_not_ref h)
  | grow E => exact absurd hr.isRef (flat_not_ref h)
  | growshrink E => exact absurd hr.isRef (flat_not_ref h)
  | limited E capacity => exact absurd hr.isRef (flat_not_ref h)
  | structT sid ts => exact absurd hr.isRef (flat_not_ref h)

variable {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}

/-- Binding the variables a construct declares in its block, one by one. -/
theorem frame_pre {sc : Nat} {si : ScopeInst} {rest0 : List (Nat × ScopeInst)}
    {future : List VarId}
    (htop : env.scopes = (sc, si) :: rest0) :
    ∀ (pre : List (VarId × Val)) (tcur : TEnv) (s : St),
    Frame m W tcur penv env s future → (pre.map Prod.fst).Nodup →
    (∀ x v, (x, v) ∈ pre → s.store.roots[RootInst.local env.act si x]? = none ∧
      ∃ lv, env.vars[x]? = some lv ∧ lv.scope = sc ∧ lv.ty.paramOk = true ∧
        HasTy m W.G s.store v lv.ty ∧
        (∀ r, Targets v r → (∃ ann, penv.ann x = some ann ∧ Gam env W.P ann r) ∧
          Older r (.local env.act si x)) ∧
        (OwnerRefTy lv.ty → ∀ r, Targets v r →
          ∃ ann, penv.ann x = some ann ∧ Gam env W.ownerP ann r)) →
    ∃ tfin, Frame m W tfin penv env { s with store := preStore env.act si pre s.store }
      (pre.map Prod.fst ++ future) ∧
      TSame tcur tfin ∧ (∀ y, y ∈ tfin.visible ↔ y ∈ pre.map Prod.fst ∨ y ∈ tcur.visible) ∧
      StoreLe s.store (preStore env.act si pre s.store) ∧
      (∀ (r : RootInst) (v : Val), s.store.roots[r]? = some v →
        (preStore env.act si pre s.store).roots[r]? = some v) ∧
      (∀ (r : RootInst) (v : Val), (preStore env.act si pre s.store).roots[r]? = some v →
        s.store.roots[r]? = some v ∨ ∃ x, x ∈ pre.map Prod.fst ∧ r = .local env.act si x)
  | [], tcur, s, hF, _, _ =>
    ⟨tcur, hF, TSame.refl _, by simp, StoreLe.refl _, fun _ _ h => h, fun _ _ h => Or.inl h⟩
  | (x, v) :: rest, tcur, s, hF, hnd, hall => by
    obtain ⟨hfree, lv, hx, hsc, hst, hv, hroot, howner⟩ := hall x v List.mem_cons_self
    have hlk : env.scopes.lookup lv.scope = some si := by rw [htop, hsc]; simp [lookup_cons]
    have hF1 := hF.bind hx hlk hst hfree hv hroot howner
    have hle1 := introduce_le s.store (.local env.act si x) v hfree
    have hnd2 : x ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := by
      simpa [List.nodup_cons] using hnd
    obtain ⟨tfin, k1, k2, k3, k4, k5, k6⟩ := frame_pre htop rest _ _ hF1 hnd2.2 (by
      intro x' v' hm
      obtain ⟨hf', lv', g1, g2, g3, g4, g5, g6⟩ := hall x' v' (List.mem_cons_of_mem _ hm)
      refine ⟨?_, lv', g1, g2, g3, g4.mono hle1, g5, g6⟩
      show (s.store.introduce (.local env.act si x) v).roots[RootInst.local env.act si x']? = none
      rw [get_introduce]
      have hne : ¬ (RootInst.local env.act si x = RootInst.local env.act si x') := by
        intro e; cases e
        exact hnd2.1 (List.mem_map.2 ⟨(x, v'), hm, rfl⟩)
      simp [hne, hf'])
    have k1' : Frame m W tfin penv env
        { s with store := preStore env.act si ((x, v) :: rest) s.store }
        (((x, v) :: rest).map Prod.fst ++ future) := by
      apply k1.future_congr
      intro y
      simp [or_assoc, or_comm]
    refine ⟨tfin, k1', (TSame.cons tcur x).trans k2, ?_, hle1.trans k4, ?_, ?_⟩
    · intro y
      rw [k3]
      simp only [List.map_cons, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    · intro r v' h
      apply k5
      show (s.store.introduce (.local env.act si x) v).roots[r]? = some v'
      rw [get_introduce]
      have hne : ¬ (RootInst.local env.act si x = r) := by
        rintro rfl; rw [hfree] at h; cases h
      simp [hne, h]
    · intro r v' h
      rcases k6 r v' h with h0 | ⟨x', hx', rfl⟩
      · have h0' : (s.store.introduce (.local env.act si x) v).roots[r]? = some v' := h0
        rw [get_introduce] at h0'
        by_cases e : RootInst.local env.act si x = r
        · exact Or.inr ⟨x, by simp, e.symm⟩
        · simp only [e, if_false] at h0'
          exact Or.inl h0'
      · exact Or.inr ⟨x', by simp [hx'], rfl⟩

theorem RetOk.tsame {a b : TEnv} {penv' : PEnv} {s' : St} {v : Val} (h : RetOk m W b penv' s' v)
    (hi : b.impl = a.impl) (hc : penv'.ctx = penv.ctx) : RetOk m W a penv s' v := by
  obtain ⟨impl, h1, h2, h3, h4⟩ := h
  exact ⟨impl, hi ▸ h1, h2, hc ▸ h3, hc ▸ h4⟩

/-- What a `return` hands over survives the release of any scope of the
activation: it points into the caller's roots and the globals only. -/
theorem RetOk.release {s2 : St} {sc : Nat} {v : Val} {future : List VarId}
    (hF : Frame m W tenv penv env s future)
    (hn : s.nextScope ≤ s2.nextScope) {si : ScopeInst} (hsi : W.base ≤ si)
    (h : RetOk m W tenv penv s2 v) : RetOk m W tenv penv (relSt env sc si s2) v := by
  obtain ⟨impl, h1, h2, h3, h4⟩ := h
  obtain ⟨hagree, _⟩ := releaseScope_roots env.vars env.act sc si s2.store
  have hsurv : ∀ r, Targets v r → ¬ ScopeRoots env.vars env.act sc si r := by
    intro r hr
    obtain ⟨declared, _, q, hq, hrq⟩ := h3 r hr
    rintro ⟨x, lv, _, _, rfl⟩
    cases q with
    | «local» y => obtain ⟨ly, _, g1, _⟩ := hrq; simp [noEnv] at g1
    | global g => cases hrq
    | param j => exact absurd (hF.pAge j _ _ _ hrq) (Nat.not_lt.2 hsi)
  refine ⟨impl, h1, ?_, h3, h4⟩
  rcases h2 with h2 | ⟨t, g1, g2⟩
  · exact Or.inl h2
  · exact Or.inr ⟨t, g1, g2.agree hagree hsurv⟩

end Goose.Core.Sound

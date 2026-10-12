import Goose.Core.Guarantees
import Goose.Core.Sound.All

/-!
The safety theorem: a module `validate` accepts never faults.

The proof is an induction on fuel over the fourteen evaluation functions
(`Goose.Core.Sound`). Its invariant is the store invariant `StoreInv` (every
stored reference or slice denotes a typed location or run, in a root that ends
no earlier than the root holding it) together with a frame per activation
(every visible variable is bound to a value of its type, and every reference
it holds points into its root annotation). This file runs that induction over
a whole run: the global initializers in order, then the entry.
-/

namespace Goose.Proofs.Safety
open Goose.Core Goose.Core.Sound Goose.Proofs.Memory

variable {m : Module}

/-- A reference that was allowed to point at the next global to be
initialized points at a typed location once that global is bound. -/
theorem held_next {G : Nat} {st : Store} {v : Val} {gl : Global} (hgl : m.globals[G]? = some gl)
    (hb : LocTy st ⟨.global G, []⟩ gl.ty) (h : Held m G st v) : Held m (G + 1) st v := by
  cases v <;> simp only [Held] at h ⊢
  · obtain ⟨T, hT, hl⟩ := h
    refine ⟨T, hT, ?_⟩
    rcases hl with hl | ⟨g, gl', hG, rfl, hg, rfl⟩
    · exact Or.inl hl
    · by_cases e : g = G
      · subst e
        rw [hgl] at hg; cases hg
        exact Or.inl hb
      · exact Or.inr ⟨g, gl', by omega, rfl, hg, rfl⟩
  · exact h

/-- Binding the next global to the value of its initializer. -/
theorem storeInv_bindGlobal {G : Nat} {s : St} {v : Val} {gl : Global} (hi : StoreInv m G s)
    (hfree : s.store.roots[RootInst.global G]? = none) (hgl : m.globals[G]? = some gl)
    (hv : FlatTy gl.ty v) :
    StoreInv m (G + 1) { s with store := s.store.introduce (.global G) v } := by
  have hle := introduce_le s.store (.global G) v hfree
  have hb : LocTy (s.store.introduce (.global G) v) ⟨.global G, []⟩ gl.ty :=
    locTy_root (by simp [get_introduce]) hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r v1 h1
    have h1' : (s.store.introduce (.global G) v).roots[r]? = some v1 := h1
    rw [get_introduce] at h1'
    by_cases e : RootInst.global G = r
    · simp only [e, if_true, Option.some.injEq] at h1'
      subst h1'
      have := flat_not_ref hv
      cases v <;> simp_all [Held, IsRef]
    · simp only [e, if_false] at h1'
      exact held_next hgl hb ((hi.live r v1 h1').mono hle)
  · intro r v1 h1 r' ht
    have h1' : (s.store.introduce (.global G) v).roots[r]? = some v1 := h1
    rw [get_introduce] at h1'
    by_cases e : RootInst.global G = r
    · simp only [e, if_true, Option.some.injEq] at h1'
      subst h1'
      exact absurd ht.isRef (flat_not_ref hv)
    · simp only [e, if_false] at h1'
      exact hi.age r v1 h1' r' ht
  · intro a si x hx
    have hx' : (s.store.introduce (.global G) v).roots[RootInst.local a si x]? ≠ none := hx
    rw [get_introduce] at hx'
    simp only [reduceCtorEq, if_false] at hx'
    exact hi.fresh a si x hx'
  · intro g gl' hg hgl'
    by_cases e : g = G
    · subst e
      rw [hgl] at hgl'; cases hgl'
      exact hb
    · exact LocTy.mono hle (hi.globals g gl' (by omega) hgl')

/-- The global initializers, run in table order from a store that holds the
first `G` globals, leave every global bound and the store invariant true. -/
theorem init_spec (hm : ModOk m) (prof : NumProfile) (fuel : Nat) :
    ∀ (k G : Nat) (s : St), G + k = m.globals.size → StoreInv m G s →
    (∀ g : Nat, G ≤ g → s.store.roots[RootInst.global g]? = none) →
    Sat (initGlobals fuel ⟨prof, m⟩ (List.range' G k)) s (fun _ s' =>
      StoreInv m m.globals.size s')
  | 0, G, s, hk, hi, _ => by
    have : G = m.globals.size := by omega
    subst this
    simp only [List.range'_zero, initGlobals, sat_pure]
    exact hi
  | k + 1, G, s, hk, hi, hl => by
    have hlt : G < m.globals.size := by omega
    have hgl : m.globals[G]? = some m.globals[G] := Array.getElem?_eq_getElem hlt
    obtain ⟨hty, ⟨tn, hte⟩, rho, st, hre, hunk, htg⟩ := hm.glob G _ hgl
    simp only [List.range'_succ, initGlobals, lookupGlobal, hgl, sat_pure_bind, sat_freshAct_bind]
    have hp : Perm m ⟨G, fun _ _ => False, st.eff, s.nextScope⟩ :=
      Or.inr ⟨hunk, fun t ht => by
        cases t with
        | global h => exact htg _ ht h rfl
        | param j => intro r hr; exact hr.elim⟩
    have hF : Frame m ⟨G, fun _ _ => False, st.eff, s.nextScope⟩ (initEnv m G)
        ⟨m, initImpl, initContext, []⟩ ⟨#[], s.nextAct, [], 0⟩ { s with nextAct := s.nextAct + 1 } :=
      { mod_t := rfl, mod_p := rfl, vars_t := rfl, vars_p := rfl, scopes_t := rfl, scopes_p := rfl
        nodup := List.nodup_nil, sorted := List.Pairwise.nil
        below := fun p hp => by cases hp
        base_le := Nat.le_refl _
        pAge := fun _ _ _ _ h => h.elim
        vis := fun x hx => by cases hx
        rooted := fun x lv si v _ h => by simp [List.lookup] at h
        inv := ⟨hi.live, hi.age, hi.fresh, hi.globals⟩ }
    refine Sat.bind ((specs_all hm prof fuel).expr _ _ _ _ _ m.globals[G].init 0 tn _ ⟨0, {}⟩ st rho hp hF
      hte hre (EffLe.refl _)) ?_
    rintro v s1 ⟨hF1, hX1, hv, _⟩
    simp only [sat_bindRoot_bind]
    have hkeep : ∀ g : Nat, G ≤ g → s1.store.roots[RootInst.global g]? = none := by
      intro g hg
      cases h1 : s1.store.roots[RootInst.global g]? with
      | none => rfl
      | some v1 => exact absurd (hl g hg) (hX1.dom _ (by rw [h1]; simp))
    refine init_spec hm prof fuel k (G + 1) _ (by omega)
      (storeInv_bindGlobal hF1.inv (hkeep G (Nat.le_refl _)) hgl (hasTy_nonref_flat hv hty.1 hty.2)) ?_
    intro g hg
    show (s1.store.introduce (.global G) v).roots[RootInst.global g]? = none
    rw [get_introduce]
    have hne : ¬ (RootInst.global G = RootInst.global g) := by
      intro e; cases e; omega
    simp only [hne, if_false]
    exact hkeep g (by omega)

theorem storeInv_initial (G : Nat) (h : G = 0) : StoreInv m G St.initial := by
  subst h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r v h; simp [St.initial, Store.empty] at h
  · intro r v h; simp [St.initial, Store.empty] at h
  · intro a si x h; simp [St.initial, Store.empty] at h
  · intro g gl h; omega

/-- A whole run of a module whose items the validator accepted does not fault
and ends, if it ends, in a store that satisfies the store invariant. -/
theorem run_spec (hm : ModOk m) (prof : NumProfile) (fuel : Nat) :
    Sat (runModule fuel ⟨prof, m⟩) St.initial (fun _ s => StoreInv m m.globals.size s) := by
  simp only [runModule, List.range_eq_range']
  refine Sat.bind (init_spec hm prof fuel m.globals.size 0 St.initial (by omega)
    (storeInv_initial 0 rfl) (fun g _ => by simp [St.initial, Store.empty])) ?_
  rintro _ s1 hi1
  obtain ⟨ctx, impl, hc, himpl, hps, _⟩ := hm.entry
  refine Sat.bind ((specs_all hm prof fuel).call m.globals.size (fun _ _ => False) 0 m.entry [] s1 ctx
    impl hc himpl hi1 (by simp [hps]) (fun i v h => by simp at h) (fun i a si x h => h.elim)
    (Or.inl (Nat.le_refl _))) ?_
  rintro v s2 ⟨hi2, _, _, _⟩
  exact hi2

/-- A module `validate` accepts never faults, at any fuel and in either numeric
profile. -/
theorem validated_never_faults (m : Module) (h : validate m = .ok ()) :
    ∀ (fuel : Nat) (profile : NumProfile) (kind : FaultKind), eval fuel profile m ≠ .fault kind := by
  intro fuel profile kind
  have hs := run_spec (validate_modOk m h) profile fuel
  unfold Sat at hs
  unfold eval
  cases hr : runModule fuel ⟨profile, m⟩ St.initial with
  | ok a s => simp
  | stop e s =>
    rw [hr] at hs
    cases e <;> simp_all

theorem validated_faultFree (m : Module) (h : validate m = .ok ()) : FaultFree m :=
  fun n p k => validated_never_faults m h n p k

/-- What acceptance means for the stores, values and locations of a run, with
every global initialized: any context of an accepted module, entered from any
store that satisfies the store invariant, with arguments of the parameters'
types that point into the roots `P` gives each parameter and into the
context's annotation of it, does not fault; it leaves the store invariant
true, every typed location typed and every stored reference of the caller in
place; and what it returns has the result type and points only into the roots
the context declares for the result. -/
theorem validated_context_sound (m : Module) (h : validate m = .ok ()) (profile : NumProfile)
    (fuel : Nat) (P : Nat → RootInst → Prop) (depth : Nat) (c : ContextId) (vals : List Val) (s : St)
    (ctx : Context) (impl : Impl) (hc : m.contexts[c]? = some ctx)
    (hi : m.impls[ctx.impl]? = some impl) (hinv : StoreInv m m.globals.size s)
    (hlen : vals.length = impl.params.size)
    (hargs : ∀ i v, vals[i]? = some v → ∃ lv, impl.vars[i]? = some lv ∧
      HasTy m m.globals.size s.store v lv.ty ∧
      ∀ r, Targets v r → ∃ ann, (ctx.varRoots.find? (·.1 == i)).map (·.2) = some ann ∧
        Gam noEnv P ann r)
    (hage : ∀ i a si x, P i (.local a si x) → si < s.nextScope) :
    Sat (enterCall fuel ⟨profile, m⟩ depth c vals) s (fun v s' =>
      StoreInv m m.globals.size s' ∧ Ext [] s s' ∧
      ((impl.results.toList = [] ∧ v = .unit) ∨
        ∃ t, impl.results.toList = [t] ∧ HasTy m m.globals.size s'.store v t) ∧
      ∀ r, Targets v r → ∃ declared, ctx.resultRoots = [declared] ∧ Gam noEnv P declared r) :=
  (specs_all (validate_modOk m h) profile fuel).call _ P depth c vals s ctx impl hc hi hinv hlen
    hargs hage (Or.inl (Nat.le_refl _))

/-- The statement the safety proof inducts with: on code of an accepted
module, each of the fourteen evaluation functions, at every fuel, does not
fault and keeps the frame invariant, and with it the store invariant, true.
Block exit is the `block` component: after a block's roots are released the
frame of the code around it holds again. -/
theorem validated_steps_keep_invariant (m : Module) (h : validate m = .ok ())
    (profile : NumProfile) : ∀ fuel, Specs m profile fuel :=
  specs_all (validate_modOk m h) profile

/-- With every global initialized, the store invariant gives the live-reference
invariant: every reference or slice a root holds denotes a typed location or a
run inside a typed array. -/
theorem liveRefs_of_storeInv {s : St} (h : StoreInv m m.globals.size s) : LiveRefs s.store := by
  intro r v hv
  have hh := h.live r v hv
  cases v <;> simp only [Held, HeldOk] at hh ⊢
  · obtain ⟨T, hT, hl⟩ := hh
    refine ⟨T, hT, ?_⟩
    rcases hl with hl | ⟨g, gl, hG, _, hg, _⟩
    · exact hl
    · have := (Array.getElem?_eq_some_iff.1 hg).1
      omega
  · obtain ⟨E, v0, es, hr, hes, hn, hT⟩ := hh
    refine ⟨E, ?_⟩
    rcases hT with hT | ⟨k, hT⟩
    · cases v0 <;> simp only [FlatTy] at hT
      simp only [Val.elems?, Option.some.injEq] at hes
      subst hes
      exact Or.inr ⟨⟨_, hr, by simpa [FlatTy] using hT⟩, _, _, hr, hn⟩
    · cases v0 <;> simp only [FlatTy] at hT
      simp only [Val.elems?, Option.some.injEq] at hes
      subst hes
      exact Or.inl ⟨k, ⟨_, hr, by simpa [FlatTy] using hT⟩, by omega⟩

/-- A run of an accepted module that ends leaves every stored reference live. -/
theorem validated_run_keeps_live_refs (m : Module) (h : validate m = .ok ()) (fuel : Nat)
    (profile : NumProfile) (a : Unit) (s : St)
    (hr : runModule fuel ⟨profile, m⟩ St.initial = .ok a s) : LiveRefs s.store := by
  have hs := run_spec (validate_modOk m h) profile fuel
  unfold Sat at hs
  rw [hr] at hs
  exact liveRefs_of_storeInv hs

end Goose.Proofs.Safety

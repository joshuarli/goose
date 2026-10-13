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
  · rename_i l
    rcases h with ⟨T, hT, hl⟩ | h
    · refine Or.inl ⟨T, hT, ?_⟩
      rcases hl with hl | ⟨g, gl', hG, hroot, hg, hpath⟩
      · exact Or.inl hl
      · by_cases e : g = G
        · subst e
          rw [hgl] at hg; cases hg
          apply Or.inl
          show LocTy st ⟨l.root, l.path⟩ T
          rw [hroot]
          simpa using hb.fieldPath hpath
        · exact Or.inr ⟨g, gl', by omega, hroot, hg, hpath⟩
    · exact Or.inr h
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
first `G` globals and nothing else, leave every global bound, nothing else in
the store, and the store invariant true. -/
theorem init_spec (hm : ModOk m) (prof : NumProfile) (fuel : Nat) :
    ∀ (k G : Nat) (s : St), G + k = m.globals.size → StoreInv m G s →
    (∀ r : RootInst, s.store.roots[r]? ≠ none → ∃ g : Nat, r = .global g ∧ g < G) →
    Sat (initGlobals fuel ⟨prof, m⟩ (List.range' G k)) s (fun _ s' =>
      StoreInv m m.globals.size s' ∧
      ∀ r : RootInst, s'.store.roots[r]? ≠ none → ∃ g : Nat, r = .global g ∧ g < m.globals.size)
  | 0, G, s, hk, hi, hdom => by
    have : G = m.globals.size := by omega
    subst this
    simp only [List.range'_zero, initGlobals, sat_pure]
    exact ⟨hi, hdom⟩
  | k + 1, G, s, hk, hi, hdom => by
    have hlt : G < m.globals.size := by omega
    have hgl : m.globals[G]? = some m.globals[G] := Array.getElem?_eq_getElem hlt
    obtain ⟨hty, ⟨tn, hte⟩, rho, st, hre, hunk, htg⟩ := hm.glob G _ hgl
    simp only [List.range'_succ, initGlobals, lookupGlobal, hgl, sat_pure_bind, sat_freshAct_bind]
    have hp : Perm m ⟨G, fun _ _ => False, st.eff, s.nextScope, fun _ _ => False, fun _ _ => False⟩ :=
      Or.inr ⟨hunk, fun t ht => by
        cases t with
        | global h => exact htg _ ht h rfl
        | param j => intro r hr; exact hr.elim⟩
    have hF : Frame m ⟨G, fun _ _ => False, st.eff, s.nextScope, fun _ _ => False, fun _ _ => False⟩
        (initEnv m G) ⟨m, initImpl, initContext, []⟩ ⟨#[], s.nextAct, [], 0⟩
        { s with nextAct := s.nextAct + 1 } :=
      { mod_t := rfl, mod_p := rfl, vars_t := rfl, vars_p := rfl, scopes_t := rfl, scopes_p := rfl
        nodup := List.nodup_nil, sorted := List.Pairwise.nil
        below := fun p hp => by cases hp
        base_le := Nat.le_refl _
        pAge := fun _ _ _ _ h => h.elim
        vis := fun x hx => by cases hx
        rooted := fun x lv si v _ h => by simp [List.lookup] at h
        inv := ⟨hi.live, hi.age, hi.fresh, hi.globals⟩
        aOlder := fun _ _ h => h.elim, dOut := fun _ _ h => h.elim, dFun := fun _ _ _ h => h.elim
        sa := fun _ _ h => h.elim
        pref := fun x cont h => by simp [PEnv.cont, initContext] at h }
    refine Sat.bind ((specs_all hm prof fuel).expr _ _ _ _ _ m.globals[G].init 0 tn _ ⟨0, {}⟩ st rho hp hF
      hte hre (EffLe.refl _)) ?_
    rintro v s1 ⟨hF1, hX1, hv, _⟩
    simp only [sat_bindRoot_bind]
    have hdom1 : ∀ r : RootInst, s1.store.roots[r]? ≠ none → ∃ g : Nat, r = .global g ∧ g < G :=
      fun r hr => hdom r (hX1.dom r hr)
    have hfree : s1.store.roots[RootInst.global G]? = none := by
      cases h1 : s1.store.roots[RootInst.global G]? with
      | none => rfl
      | some v1 =>
        obtain ⟨g, e, hg⟩ := hdom1 _ (by rw [h1]; simp)
        cases e; omega
    refine init_spec hm prof fuel k (G + 1) _ (by omega)
      (storeInv_bindGlobal hF1.inv hfree hgl
        (hasTy_nonref_flat hv (paramOk_of_storable hty.1) hty.2)) ?_
    intro r hr
    have hr' : (s1.store.introduce (.global G) v).roots[r]? ≠ none := hr
    rw [get_introduce] at hr'
    by_cases e : RootInst.global G = r
    · exact ⟨G, e.symm, Nat.lt_succ_self _⟩
    · simp only [e, if_false] at hr'
      obtain ⟨g, e', hg⟩ := hdom1 r hr'
      exact ⟨g, e', Nat.lt_succ_of_lt hg⟩

theorem storeInv_initial (G : Nat) (h : G = 0) : StoreInv m G St.initial := by
  subst h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r v h; simp [St.initial, Store.empty] at h
  · intro r v h; simp [St.initial, Store.empty] at h
  · intro a si x h; simp [St.initial, Store.empty] at h
  · intro g gl h; omega

/-- A whole run of a module whose items the validator accepted does not fault
and ends, if it ends, in a store that holds the globals only and satisfies the
store invariant. -/
theorem run_spec (hm : ModOk m) (prof : NumProfile) (fuel : Nat) :
    Sat (runModule fuel ⟨prof, m⟩) St.initial (fun _ s => StoreInv m m.globals.size s ∧
      ∀ r : RootInst, s.store.roots[r]? ≠ none → ∃ g : Nat, r = .global g ∧ g < m.globals.size) := by
  simp only [runModule, List.range_eq_range']
  refine Sat.bind (init_spec hm prof fuel m.globals.size 0 St.initial (by omega)
    (storeInv_initial 0 rfl) (fun r hr => by simp [St.initial, Store.empty] at hr)) ?_
  rintro _ s1 ⟨hi1, hdom1⟩
  obtain ⟨ctx, impl, hc, himpl, hps, _⟩ := hm.entry
  obtain ⟨impl', himpl', hcOk⟩ := hm.ctx _ ctx hc
  rw [himpl] at himpl'
  cases himpl'
  refine Sat.bind ((specs_all hm prof fuel).call m.globals.size (fun _ _ => False) (fun _ _ => False)
    (fun _ _ => False) 0 m.entry [] s1 ctx impl hc himpl hi1 (by simp [hps])
    (fun i v h => by simp at h) (fun i a si x h => h.elim) (fun _ _ h => h.elim)
    (fun _ _ h => h.elim) (fun _ _ _ h => h.elim) (fun _ _ h => h.elim)
    (fun x cont h => by
      have := (hcOk.content x cont h).1
      omega)
    (Or.inl (Nat.le_refl _))) ?_
  rintro v s2 ⟨hi2, hX2, _, _, _⟩
  exact ⟨hi2, fun r hr => hdom1 r (hX2.dom r hr)⟩

/-- A module `validate` accepts never faults, at any fuel and in either numeric
profile.

A fault is one of six things the evaluator can meet: an access through a root
that is gone or along a path outside its object, a value of the wrong shape
where an operation needs an integer, a boolean, a reference, a slice or an
array, a missing table entry, a call with the wrong number of arguments, or a
`break`, `continue` or `return` leaving an expression or a body. Aborts, exits
and running out of fuel are not faults.

This is not type preservation: the evaluator stores any value anywhere, so an
unchecked module can put a boolean in an integer variable and run to the end.
That every variable of an accepted module holds a value of its type at every
step is part of the invariant the proof carries
(`validated_steps_keep_invariant`). And it says nothing of mutability: the
evaluator has no read-only storage, so the rule that writes go through mutable
places has no semantic statement here. -/
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
the context declares for the result.

`D` and `A` describe the slice variables the caller passes by reference: each
holds a slice of its element type rooted within `A`, each parameter that
refers to one has content roots that denote exactly `A` of it, and on return
each still holds such a slice. A caller that passes none takes both empty. -/
theorem validated_context_sound (m : Module) (h : validate m = .ok ()) (profile : NumProfile)
    (fuel : Nat) (P : Nat → RootInst → Prop) (D : RootInst → Ty → Prop)
    (A : RootInst → RootInst → Prop) (depth : Nat) (c : ContextId) (vals : List Val) (s : St)
    (ctx : Context) (impl : Impl) (hc : m.contexts[c]? = some ctx)
    (hi : m.impls[ctx.impl]? = some impl) (hinv : StoreInv m m.globals.size s)
    (hlen : vals.length = impl.params.size)
    (hargs : ∀ i v, vals[i]? = some v → ∃ lv, impl.vars[i]? = some lv ∧
      HasTy m m.globals.size s.store v lv.ty ∧
      ∀ r, Targets v r → ∃ ann, (ctx.varRoots.find? (·.1 == i)).map (·.2) = some ann ∧
        Gam noEnv P ann r)
    (hage : ∀ i a si x, P i (.local a si x) → si < s.nextScope)
    (hAO : ∀ r t, A r t → Older t r)
    (hDout : ∀ r E, D r E → ∃ a si x, r = RootInst.local a si x ∧ si < s.nextScope)
    (hDfun : ∀ r E E', D r E → D r E' → E = E')
    (hSA : OuterOk m m.globals.size D A s)
    (hcont : ∀ x cont, (ctx.contentRoots.find? (·.1 == x)).map (·.2) = some cont →
      PRef P D A ⟨m, impl, ctx, []⟩ impl.vars x cont) :
    Sat (enterCall fuel ⟨profile, m⟩ depth c vals) s (fun v s' =>
      StoreInv m m.globals.size s' ∧ Ext [] (fun r => ∃ E, D r E) s s' ∧
      OuterOk m m.globals.size D A s' ∧
      ((impl.results.toList = [] ∧ v = .unit) ∨
        ∃ t, impl.results.toList = [t] ∧ HasTy m m.globals.size s'.store v t) ∧
      ∀ r, Targets v r → ∃ declared, ctx.resultRoots = [declared] ∧ Gam noEnv P declared r) :=
  (specs_all (validate_modOk m h) profile fuel).call _ P D A depth c vals s ctx impl hc hi hinv hlen
    hargs hage hAO hDout hDfun hSA hcont (Or.inl (Nat.le_refl _))

/-- The statement the safety proof inducts with: on code of an accepted
module, each of the fourteen evaluation functions, at every fuel, does not
fault and keeps the frame invariant, and with it the store invariant, true.
Block exit is the `block` component: after a block's roots are released the
frame of the code around it holds again. -/
theorem validated_steps_keep_invariant (m : Module) (h : validate m = .ok ())
    (profile : NumProfile) : ∀ fuel, Specs m profile fuel :=
  specs_all (validate_modOk m h) profile

/-- A run of an accepted module that returns leaves every global holding a
value of the global's declared type. The same holds of every variable at every
step, which is part of the frame invariant (`validated_steps_keep_invariant`):
nothing in the evaluator checks the type of a value it stores, so this is what
acceptance adds beyond the absence of faults. It is stated here only for the
globals of a run that returns, where it needs no vocabulary. -/
theorem validated_run_keeps_globals_typed (m : Module) (h : validate m = .ok ()) (fuel : Nat)
    (profile : NumProfile) (a : Unit) (s : St)
    (hr : runModule fuel ⟨profile, m⟩ St.initial = .ok a s) :
    ∀ (g : Nat) (gl : Global), m.globals[g]? = some gl →
      ∃ v, s.store.roots[RootInst.global g]? = some v ∧ FlatTy gl.ty v := by
  have hs := run_spec (validate_modOk m h) profile fuel
  unfold Sat at hs
  rw [hr] at hs
  intro g gl hg
  obtain ⟨v, hv, hT⟩ := hs.1.globals g gl (Array.getElem?_eq_some_iff.1 hg).1 hg
  obtain ⟨old, ho, hget⟩ := (read_ok_iff _ _ _).1 hv
  rw [get_nil] at hget
  have e : old = v := by simpa using hget
  subst e
  exact ⟨_, ho, hT⟩

end Goose.Proofs.Safety

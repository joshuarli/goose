import Goose.Core.Sound.StepAux

/-!
The step for entering a callee: a fresh activation whose parameters are bound
in the body block's scope instance.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {plans : Array (Array DemandPoint)} {n : Nat}

/-- The successful body replay fixes one effect regardless of the witness
used to package its result roots and state. -/
private theorem contextEff_unique {impl : Impl} {ctx : Context} {E E' : Eff}
    (h : ContextEff m impl ctx E) (h' : ContextEff m impl ctx E') : E = E' := by
  rcases h with ⟨rho, range, state, hrun, hE⟩
  rcases h' with ⟨rho', range', state', hrun', hE'⟩
  rw [hrun] at hrun'
  cases hrun'
  exact hE.symm.trans hE'

/-! ### Entering a callee -/

private theorem pre_fst_range (f : Param × Val → VarId × Val) (hf : ∀ p v, f (p, v) = (p.var, v)) :
    ∀ (ps : List Param) (vs : List Val) (k : Nat), ps.length = vs.length →
    (∀ i p, ps[i]? = some p → p.var = k + i) →
    ((ps.zip vs).map f).map Prod.fst = List.range' k ps.length
  | [], vs, k, _, _ => by simp
  | p :: ps, [], k, hl, _ => by simp at hl
  | p :: ps, v :: vs, k, hl, hvar => by
    have h0 : p.var = k := by simpa using hvar 0 p rfl
    have ih := pre_fst_range f hf ps vs (k + 1) (by simpa using hl) (fun i p' h => by
      have := hvar (i + 1) p' (by simpa using h)
      rw [this]; omega)
    simp only [List.zip_cons_cons, List.map_cons, hf, List.length_cons, List.range'_succ, ih, h0]

private theorem pre_mem (f : Param × Val → VarId × Val) (hf : ∀ p v, f (p, v) = (p.var, v)) :
    ∀ (ps : List Param) (vs : List Val) (x : VarId) (v : Val), (x, v) ∈ (ps.zip vs).map f →
    ∃ (i : Nat) (p : Param), ps[i]? = some p ∧ vs[i]? = some v ∧ p.var = x
  | [], vs, x, v, h => by simp at h
  | p :: ps, [], x, v, h => by simp at h
  | p :: ps, v' :: vs, x, v, h => by
    simp only [List.zip_cons_cons, List.map_cons, hf, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨0, p, rfl, rfl, rfl⟩
    · obtain ⟨i, p', h1, h2, h3⟩ := pre_mem f hf ps vs x v h
      exact ⟨i + 1, p', by simpa using h1, by simpa using h2, h3⟩

set_option maxHeartbeats 1600000 in
private theorem enterCall_of_bodyContext (hm : ModOk m) (ih : Specs m prof plans n) :
  ∀ (G : Nat) (P : Nat → RootInst → Prop) (D : RootInst → Ty → Prop)
    (A : RootInst → RootInst → Prop) (depth : Nat) (c : ContextId) (vals : List Val) (s : St)
    (ctx : Context) (impl : Impl) (E : Eff) (observation : Observation)
    (root : EvaluationContext m plans [] (.block impl.body) .block),
    root.ActiveMatches (implEnv m impl) →
    root.AccessMatches { implEnv m impl with visible := [] } ⟨m, impl, ctx, []⟩ →
    ContextEff m impl ctx E →
    m.contexts[c]? = some ctx → m.impls[ctx.impl]? = some impl →
    StoreInv m G s (ObservationDemand observation) →
    ObservedSafe m ⟨G, P, E, s.nextScope, D, A⟩ (root.mayShrink P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m P D observation s.store) →
    ShrinkProtected D A (root.mayShrink P observation) → vals.length = impl.params.size →
    (∀ i v, vals[i]? = some v → ∃ lv, impl.vars[i]? = some lv ∧ HasTy m G s.store v lv.ty ∧
      ∀ r, Targets v r → ∃ ann, (ctx.varRoots.find? (·.1 == i)).map (·.2) = some ann ∧
        Gam noEnv P ann r) →
    (∀ i a si x, P i (.local a si x) → si < s.nextScope) →
    (∀ r t, A r t → Older t r) →
    (∀ r E, D r E → ∃ a si x, r = RootInst.local a si x ∧ si < s.nextScope) →
    (∀ r E E', D r E → D r E' → E = E') →
    OuterOk m G D A s →
    (∀ x cont, (ctx.contentRoots.find? (·.1 == x)).map (·.2) = some cont →
      PRef P D A ⟨m, impl, ctx, []⟩ impl.vars x cont) →
    (m.globals.size ≤ G ∨ SumOk G P impl ctx) →
    Sat (enterCall (n + 1) ⟨prof, m⟩ depth c vals) s (fun v s' =>
      StoreInv m G s' (ObservationDemand observation) ∧
      CallTransition m G observation.roots observation.values
        (fun r => ∃ element, D r element) s s' ∧
      ObservedSafe m ⟨G, P, E, s.nextScope, D, A⟩ (root.mayShrink P observation) observation s'.store ∧
      PilotStoreLe m s s' ∧
      OuterOk m G D A s' ∧
      ((impl.results.toList = [] ∧ v = .unit) ∨
        ∃ t, impl.results.toList = [t] ∧ HasTy m G s'.store v t) ∧
      (∀ r, Targets v r → ∃ declared, ctx.resultRoots = [declared] ∧ Gam noEnv P declared r) ∧
      (m.profile = .shrink → ClassifiedParameters m P D observation s'.store))
 := by
  intro G P D A depth c vals s ctx impl E observation root hActiveRoot hAccessRoot hEff
    hctx himpl hInv hObserved hClass hProtected hlen hargs hPage hAO hDout hDfun hSA hcont hperm
  obtain ⟨impl', himpl', hcOk⟩ := hm.ctx c ctx hctx
  rw [himpl] at himpl'
  cases himpl'
  have hiOk := hm.impl _ _ himpl
  have hpar := hiOk.params
  have hsc0 := hiOk.bodyScope
  obtain ⟨bodyTy, tnb, htb, hresTy⟩ := hiOk.body
  obtain ⟨rho, rng, st, hrb, hck, hcs⟩ := hcOk.body
  have hEffEq : E = st.eff := contextEff_unique hEff ⟨rho, rng, st, hrb, rfl⟩
  subst E
  simp only [enterCall]
  by_cases hd : depth ≥ maxCallDepth
  · simp only [hd, if_true, sat_timeout_bind]
  · simp only [hd, if_false, lookupContext, lookupImpl, hctx, himpl, sat_pure_bind, hlen, if_true,
      sat_freshAct_bind]
    have hpW : Perm m ⟨G, P, st.eff, s.nextScope, D, A⟩ := by
      rcases hperm with h | ⟨sm, hs, hall⟩
      · exact Or.inl h
      · obtain ⟨hu, h1, h2, h3, _⟩ := checkSummary_ok _ _ _ _ hcs sm hs
        refine Or.inr ⟨hu, fun t ht => ?_⟩
        rcases ht with ht | ht | ht | ht
        · exact hall t (Or.inl (h1 t ht))
        · exact hall t (Or.inr (Or.inl (h2 t ht)))
        · exact hall t (Or.inr (Or.inr (Or.inl (h3 t ht))))
        · exact hall t (Or.inr (Or.inr (Or.inr (checkSummary_shrinks_ok m impl ctx st.eff hcs sm hs t ht))))
    have hF0 : Frame m ⟨G, P, st.eff, s.nextScope, D, A⟩ { implEnv m impl with visible := [] }
        ⟨m, impl, ctx, []⟩ ⟨impl.vars, s.nextAct, [], depth + 1⟩
        { s with nextAct := s.nextAct + 1 } root.inputFuture :=
      { mod_t := rfl, mod_p := rfl, vars_t := rfl, vars_p := rfl
        scopes_t := rfl, scopes_p := rfl
        nodup := List.nodup_nil, sorted := List.Pairwise.nil
        below := fun p hp => by cases hp
        base_le := Nat.le_refl _
        pAge := hPage
        vis := fun x hx => by cases hx
        bindings := fun x hx => by cases hx
        storage := by
          rintro r T ⟨x, lv, si, _, hscope, _⟩ v hv
          simp [List.lookup] at hscope
        rooted := fun x lv si v _ h => by simp [List.lookup] at h
        inv := {
          live := by
            intro r v hv hd
            cases r with
            | global g => exact hInv.live _ v hv trivial
            | «local» a si x =>
              rcases hd with ⟨_, _, _, lv, _, hscope⟩
              simp [List.lookup] at hscope
          age := hInv.age, fresh := hInv.fresh, globals := hInv.globals
          globalNonRefs := hInv.globalNonRefs }
        aOlder := hAO, dOut := hDout, dFun := hDfun, sa := hSA
        pref := fun x cont h => hcont x cont h }
    have hpreFst := pre_fst_range (fun x => (x.fst.var, x.snd)) (fun _ _ => rfl) impl.params.toList
      vals 0 (by simp [hlen]) (fun i p h => by
        have := (hpar i p (by simpa using h)).1
        simp [this])
    generalize impl.body = body at *
    obtain ⟨sc, stmts, value⟩ := body
    have hsc : sc = 0 := hsc0
    subst hsc
    obtain ⟨_, env1, tn1, env2, tn2, hdp, hts, htv⟩ := tyBlock_ok _ _ _ _ _ _ _ _ htb
    obtain ⟨hsame, hvisT, _, _⟩ := declarePre_ok _ _ _ _ _ _ hdp
    obtain ⟨_, st2, hrs, hrv, _⟩ := rpBlockValue_ok _ _ _ _ _ _ _ _ _ hrb
    have hpreOk : PreOk m ⟨G, P, st.eff, s.nextScope, D, A⟩ ⟨m, impl, ctx, []⟩
        { vars := impl.vars, act := s.nextAct, scopes := [(0, s.nextScope)], depth := depth + 1 } 0 0
        (impl.params.size + 0) s.store
        (List.map (fun x => (x.fst.var, x.snd)) (impl.params.toList.zip vals)) := by
      refine ⟨by rw [hpreFst]; exact List.nodup_range', ?_⟩
      intro x v hxv
      obtain ⟨i, p, h1, h2, h3⟩ := pre_mem _ (fun _ _ => rfl) _ _ x v hxv
      have h1' : impl.params[i]? = some p := by simpa using h1
      obtain ⟨hvar, lv, hlv, hlsc, hlst⟩ := hpar i p h1'
      rw [hvar] at h3
      subst h3
      obtain ⟨lv', hlv', hty, hroots⟩ := hargs i v h2
      rw [hlv] at hlv'
      cases hlv'
      refine ⟨Nat.zero_le _, by simpa using (Array.getElem?_eq_some_iff.1 h1').1, lv, hlv, hlsc, hlst,
        hty, fun r hr => ?_⟩
      obtain ⟨ann, ha, hg⟩ := hroots r hr
      exact ⟨ann, ha, gam_of_noEnv hg⟩
    have hvisB : ∀ y, y ∈ env1.visible ↔
        y ∈ (List.map (fun x => (x.fst.var, x.snd)) (impl.params.toList.zip vals)).map Prod.fst ∨
          y ∈ ([] : List VarId) := by
      intro y
      rw [hvisT y, hpreFst]
      simp [implEnv, List.range_eq_range']
    have hkeep : ∀ y, RootRef.local y ∈ rho → ¬ (0 ≤ y ∧ y < st.nextVar) := by
      intro y hy
      cases value with
      | none => rw [hrv.1] at hy; cases hy
      | some e => exact absurd hy ((checkResultV_ok _ _ (hck rfl)).1 y)
    have hactive : root.ActiveMatches env1 := by
      have hvisible : ∀ x, x ∈ env1.visible ↔ x ∈ (implEnv m impl).visible := by
        intro x
        rw [hvisB x, hpreFst]
        simp [implEnv, List.range_eq_range']
      cases root <;> intro x <;> exact (hActiveRoot x).trans (hvisible x).symm
    refine Sat.bind (ih.block [] 0 stmts value root observation ⟨G, P, st.eff, s.nextScope, D, A⟩ { implEnv m impl with visible := [] } env1
      env2 ⟨m, impl, ctx, []⟩ ⟨impl.vars, s.nextAct, [], depth + 1⟩ { s with nextAct := s.nextAct + 1 }
      _ tn1 tn2 tnb bodyTy _ st2 st rho 0 hactive hAccessRoot hProtected hObserved hClass hpW hF0 (by simp [implEnv])
      ⟨hsame.mod, hsame.impl, hsame.vars, hsame.loops, hsame.inExpr, hsame.scopes,
        fun _ h => by cases h⟩ hvisB hpreOk (Nat.zero_le _) hts
      (by cases value with
          | none => exact htv.1
          | some e => exact htv)
      hrs
      (by cases value with
          | none => exact hrv
          | some e => exact hrv)
      (EffLe.refl _) hkeep) ?_
    rintro fl s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetained1, hPilot1, hfl, hClass1⟩
    have hXs : Footprint [] (fun r => ∃ E, D r E) s s1 :=
      (Footprint.of_eq (s := s) (s' := { s with nextAct := s.nextAct + 1 }) rfl rfl).trans hX1
    have hInv1 := (hF1.callDemand hObserved1.typed (fun r element hd => by
      obtain ⟨v, hv, ht, _⟩ := hF1.sa r element hd
      exact ⟨v, hv, ht⟩)).observationDemand
    have hTransition : CallTransition m G observation.roots observation.values
        (fun r => ∃ element, D r element) s s1 :=
      ⟨hXs, hRoots1, hValues1⟩
    cases fl with
    | normal v =>
      simp only [expectReturned, sat_pure]
      obtain ⟨hv, hg, hdv⟩ := hfl
      refine ⟨hInv1, hTransition, hObserved1, hPilot1, hF1.sa, ?_, ?_, hClass1⟩
      · rcases hresTy with ⟨hnil, rfl⟩ | ⟨t, hone, hsome, hnone⟩
        · exact Or.inl ⟨hnil, hv⟩
        · cases value with
          | none =>
            have := hnone rfl
            simp only [Block.diverges] at this
            rw [this] at hdv; cases hdv
          | some e =>
            have := hsome rfl
            subst this
            exact Or.inr ⟨_, hone, hv⟩
      · intro r hr
        cases value with
        | none =>
          obtain ⟨q, hq, _⟩ := hg r hr
          rw [hrv.1] at hq; cases hq
        | some e =>
          obtain ⟨hnl, declared, hd', hsub⟩ := checkResultV_ok _ _ (hck rfl)
          exact ⟨declared, hd', (gam_noEnv (hg r hr) hnl).subset hsub⟩
    | brk => exact absurd rfl hfl.1
    | cont => exact absurd rfl hfl
    | ret v =>
      simp only [expectReturned, sat_pure]
      obtain ⟨_, impl'', hi'', hres'', hroots''⟩ := hfl
      cases hi''
      exact ⟨hInv1, hTransition, hObserved1, hPilot1, hF1.sa, hres'', hroots'', hClass1⟩



set_option maxHeartbeats 1600000 in
theorem step_call (hm : ModOk m) (ih : Specs m prof plans n) :
    CallSpec m prof plans (n + 1) := by
  intro G P D A depth c vals s ctx impl E observation root hOwner hEff hctx himpl
    hInv hObserved hClass hProtected hlen hargs hPage hAO hDout hDfun hSA hcont hperm
  let bodyContext := root.callBody hOwner hctx himpl
  have hvisible : ∀ x, x ∈ (implEnv m impl).visible ↔
      x ∈ impl.params.toList.map (·.var) := by
    intro x
    change x ∈ List.range impl.params.size ↔ x ∈ impl.params.toList.map (·.var)
    constructor
    · intro hx
      have hlt := List.mem_range.mp hx
      let parameter := impl.params[x]
      have hp : impl.params[x]? = some parameter := Array.getElem?_eq_getElem hlt
      exact List.mem_map.mpr ⟨parameter,
        List.mem_of_getElem? (by simpa using hp), (hm.impl _ impl himpl).params x parameter hp |>.1⟩
    · intro hx
      obtain ⟨parameter, hmem, hvar⟩ := List.mem_map.mp hx
      obtain ⟨index, hp⟩ := List.mem_iff_getElem?.mp hmem
      have hp' : impl.params[index]? = some parameter := by simpa using hp
      have hindex := (hm.impl _ impl himpl).params index parameter hp'
      rw [hindex.1] at hvar
      subst x
      exact List.mem_range.mpr (Array.getElem?_eq_some_iff.mp hp').1
  have hActive := root.callBody_activeMatches hOwner hctx himpl (implEnv m impl) hvisible
  have hAccess := root.callBody_accessMatches hOwner hctx himpl
    { implEnv m impl with visible := [] } ⟨m, impl, ctx, []⟩ rfl rfl rfl rfl rfl
  have hMay := root.callBody_mayShrink_iff hOwner hctx himpl P observation
  have hObservedBody := hObserved.weakenShrinking (fun r hr => (hMay r).mp hr)
  have hProtectedBody := hProtected.mono (fun _ _ h => h) (fun _ _ h => h)
    (fun r hr => (hMay r).mp hr)
  refine (enterCall_of_bodyContext hm ih G P D A depth c vals s ctx impl E observation
    bodyContext hActive hAccess hEff hctx himpl hInv hObservedBody hClass hProtectedBody hlen
    hargs hPage hAO hDout hDfun hSA hcont hperm).mono ?_
  rintro v s' ⟨hInv', hTransition, hObserved', hPilot, hOuter, hResult, hRoots, hClass'⟩
  exact ⟨hInv', hTransition,
    hObserved'.weakenShrinking (fun r hr => (hMay r).mpr hr), hPilot, hOuter, hResult, hRoots, hClass'⟩

end Goose.Core.Sound

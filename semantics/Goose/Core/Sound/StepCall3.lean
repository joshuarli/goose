import Goose.Core.Sound.StepCall2

/-!
The step for entering a callee: a fresh activation whose parameters are bound
in the body block's scope instance.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {n : Nat}

set_option maxHeartbeats 1600000 in
theorem step_call (hm : ModOk m) (ih : Specs m prof n) : CallSpec m prof (n + 1) := by
  intro G P D A depth c vals s ctx impl hctx himpl hInv hlen hargs hPage hAO hDout hDfun hSA hcont hperm
  obtain ⟨impl', himpl', hcOk⟩ := hm.ctx c ctx hctx
  rw [himpl] at himpl'
  cases himpl'
  have hiOk := hm.impl _ _ himpl
  have hpar := hiOk.params
  have hsc0 := hiOk.bodyScope
  obtain ⟨bodyTy, tnb, htb, hresTy⟩ := hiOk.body
  obtain ⟨rho, rng, st, hrb, hck, hcs⟩ := hcOk.body
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
        rcases ht with ht | ht | ht
        · exact hall t (Or.inl (h1 t ht))
        · exact hall t (Or.inr (Or.inl (h2 t ht)))
        · exact hall t (Or.inr (Or.inr (h3 t ht)))
    have hF0 : Frame m ⟨G, P, st.eff, s.nextScope, D, A⟩ { implEnv m impl with visible := [] }
        ⟨m, impl, ctx, []⟩ ⟨impl.vars, s.nextAct, [], depth + 1⟩
        { s with nextAct := s.nextAct + 1 } :=
      { mod_t := rfl, mod_p := rfl, vars_t := rfl, vars_p := rfl
        scopes_t := rfl, scopes_p := rfl
        nodup := List.nodup_nil, sorted := List.Pairwise.nil
        below := fun p hp => by cases hp
        base_le := Nat.le_refl _
        pAge := hPage
        vis := fun x hx => by cases hx
        rooted := fun x lv si v _ h => by simp [List.lookup] at h
        inv := ⟨hInv.live, hInv.age, hInv.fresh, hInv.globals⟩
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
    refine Sat.bind (ih.block ⟨G, P, st.eff, s.nextScope, D, A⟩ { implEnv m impl with visible := [] } env1
      env2 ⟨m, impl, ctx, []⟩ ⟨impl.vars, s.nextAct, [], depth + 1⟩ { s with nextAct := s.nextAct + 1 }
      _ 0 stmts value tn1 tn2 tnb bodyTy _ st2 st rho 0 hpW hF0 (by simp [implEnv])
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
    rintro fl s1 ⟨hF1, hX1, hfl⟩
    have hXs : Ext [] (fun r => ∃ E, D r E) s s1 :=
      (Ext.of_eq (s := s) (s' := { s with nextAct := s.nextAct + 1 }) rfl rfl).trans hX1
    cases fl with
    | normal v =>
      simp only [expectReturned, sat_pure]
      obtain ⟨hv, hg, hdv⟩ := hfl
      refine ⟨hF1.inv, hXs, hF1.sa, ?_, ?_⟩
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
      exact ⟨hF1.inv, hXs, hF1.sa, hres'', hroots''⟩

end Goose.Core.Sound

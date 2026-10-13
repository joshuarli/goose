import Goose.Core.Sound.StepBlock

/-!
The steps for a statement list and for a block.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {n : Nat}

set_option maxHeartbeats 800000 in
theorem step_stmts (ih : Specs m prof n) : StmtsSpec m prof (n + 1) := by
  intro W tenv tenv' penv env s sc ss tn tn' rst rst' lo hp hF hsc hT hlo ht hr hE
  cases ss with
  | nil =>
    simp only [tyStmts] at ht; inv at ht
    simp only [rpStmts] at hr; inv at hr
    obtain ⟨rfl, rfl⟩ := ht
    subst hr
    simp only [execStmts, sat_pure]
    exact ⟨⟨tenv', TSame.refl _, hF, fun _ _ => rfl⟩, (Ext.refl _ _ _).toS, hT,
      (⟨trivial, rfl⟩ : True ∧ stmtsDiverge m.noReturn [] = false)⟩
  | cons st rest =>
    simp only [tyStmts] at ht; inv at ht
    simp only [rpStmts] at hr; inv at hr
    obtain ⟨tenv1, t1, hts, htr⟩ := ht
    obtain ⟨r1, hrs, hrr⟩ := hr
    have hm1 := rpStmt_mono hrs
    have hm2 := rpStmts_mono hrr
    simp only [execStmts]
    refine Sat.bind (ih.stmt W tenv tenv1 penv env s sc st tn t1 rst r1 lo hp hF hsc hT hlo hts hrs
      (hm2.2.trans hE)) ?_
    rintro fl s1 ⟨hF1, hS1, hX1, hT1, hfl⟩
    cases fl with
    | normal v =>
      refine (ih.stmts W tenv1 tenv' penv env s1 sc rest t1 tn' r1 rst' lo hp hF1
        (by rw [hS1.scopes]; exact hsc) hT1 (Nat.le_trans hlo hm1.1) htr hrr hE).mono ?_
      rintro fl2 s2 ⟨⟨tenv2, hS2, hF2, hn2⟩, hX2, hT2, hfl2⟩
      refine ⟨⟨tenv2, hS1.trans hS2, hF2, hn2⟩, hX1.trans hX2, hT2, ?_⟩
      cases fl2 with
      | normal v2 => exact ⟨hfl2.1, by simp [stmtsDiverge, hfl, hfl2.2]⟩
      | brk => exact ⟨by rw [← hS1.loops]; exact hfl2.1, by simp [stmtsHaveBreak, hfl2.2]⟩
      | cont => exact (by rw [← hS1.loops]; exact hfl2)
      | ret v2 => exact ⟨by rw [← hS1.inExpr]; exact hfl2.1, hfl2.2.tsame hS1.impl rfl⟩
    | brk =>
      simp only [sat_pure]
      exact ⟨⟨tenv1, hS1, hF1, fun v h => by cases h⟩, hX1, hT1.ext (fun _ h => h) hm2.1,
        hfl.1, by simp [stmtsHaveBreak, hfl.2]⟩
    | cont =>
      simp only [sat_pure]
      exact ⟨⟨tenv1, hS1, hF1, fun v h => by cases h⟩, hX1, hT1.ext (fun _ h => h) hm2.1, hfl⟩
    | ret v =>
      simp only [sat_pure]
      exact ⟨⟨tenv1, hS1, hF1, fun v h => by cases h⟩, hX1, hT1.ext (fun _ h => h) hm2.1, hfl⟩

set_option maxHeartbeats 1600000 in
theorem step_block (ih : Specs m prof n) : BlockSpec m prof (n + 1) := by
  intro W tenv tenv1 tenv2 penv env s pre sc stmts value tn1 tn2 tn3 ty rst1 rst2 rst3 rho lo
    hp hF hsc hsame hvis hpre hlo hts htv hrs hrv hE hkeep
  simp only [execBlock, sat_freshScope_bind, sat_bindAll_bind]
  have hF0 := hF.push hsc
  have hfreshAll : ∀ x, s.store.roots[RootInst.local env.act s.nextScope x]? = none := fun x => by
    cases h : s.store.roots[RootInst.local env.act s.nextScope x]? with
    | none => rfl
    | some v => exact absurd (hF.inv.fresh _ _ _ (by rw [h]; simp)) (Nat.lt_irrefl _)
  obtain ⟨hnd, hpreAll⟩ := hpre
  obtain ⟨tfin, hFb, hSb, hvisb, hleb, hkeepb, hbackb⟩ :=
    frame_pre (env := { env with scopes := (sc, s.nextScope) :: env.scopes }) (rest0 := env.scopes)
      rfl pre _ _ hF0 hnd (by
        intro x v hm
        obtain ⟨_, _, lv, g1, g2, g3, g4, g5⟩ := hpreAll x v hm
        refine ⟨hfreshAll x, lv, g1, g2, g3, g4, fun r hr => ⟨g5 r hr, ?_⟩⟩
        rcases hasTy_target_dom g4 hr with ⟨g, rfl⟩ | hd
        · trivial
        · cases r with
          | global g => trivial
          | «local» a si' x' => exact Nat.le_of_lt (hF.inv.fresh _ _ _ hd))
  have hF1 := hFb.tenv_congr (t2 := tenv1) (hsame.mod.trans hSb.mod.symm)
    (hsame.vars.trans hSb.vars.symm) (hsame.scopes.trans hSb.scopes.symm)
    (fun y hy => (hvisb y).2 ((hvis y).1 hy))
  have hTop : TopB { env with scopes := (sc, s.nextScope) :: env.scopes } lo rst1.nextVar
      { s with nextScope := s.nextScope + 1,
               store := preStore env.act s.nextScope pre s.store } := by
    intro sc' si' rest' he y hy
    cases he
    cases hv : (preStore env.act s.nextScope pre s.store).roots[RootInst.local env.act s.nextScope y]? with
    | none => exact absurd hv hy
    | some v' =>
      rcases hbackb _ v' hv with h0 | ⟨x, hx, e⟩
      · have := hfreshAll y
        rw [this] at h0; cases h0
      · cases e
        obtain ⟨⟨x', v''⟩, hm, rfl⟩ := List.mem_map.1 hx
        obtain ⟨g1, g2, _⟩ := hpreAll _ _ hm
        exact ⟨g1, g2⟩
  have hE2 : EffLe rst2.eff W.E := by
    cases value with
    | none => rw [← hrv.2]; exact hE
    | some e => exact (rpExpr_mono hrv).2.trans hE
  -- Leaving the block from a state reached inside it.
  have exit : ∀ (s2 : St) (tf : TEnv),
      Frame m W tf { penv with scopes := sc :: penv.scopes }
        { env with scopes := (sc, s.nextScope) :: env.scopes } s2 →
      TSame tenv1 tf →
      ExtS { env with scopes := (sc, s.nextScope) :: env.scopes } (Dset W)
        { s with nextScope := s.nextScope + 1,
                 store := preStore env.act s.nextScope pre s.store } s2 →
      Frame m W tenv penv env (relSt env sc s.nextScope s2) ∧
      Ext (insts env) (Dset W) s (relSt env sc s.nextScope s2) := by
    intro s2 tf hFf hSf hXf
    have hdom : ∀ (r : RootInst), s2.store.roots[r]? ≠ none →
        s.store.roots[r]? ≠ none ∨ ScopeRoots env.vars env.act sc s.nextScope r := by
      intro r hr
      rcases hXf.dom r hr with h0 | ⟨x, lv, si', rest', he, hx, rfl⟩
      · cases hv : (preStore env.act s.nextScope pre s.store).roots[r]? with
        | none => exact absurd hv h0
        | some v' =>
          rcases hbackb r v' hv with h1 | ⟨x, hx, rfl⟩
          · exact Or.inl (by rw [h1]; simp)
          · obtain ⟨⟨x', v''⟩, hm, rfl⟩ := List.mem_map.1 hx
            obtain ⟨_, _, lv, g1, g2, _⟩ := hpreAll _ _ hm
            exact Or.inr ⟨x', lv, g1, g2, rfl⟩
      · cases he
        exact Or.inr ⟨x, lv, hx, rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · refine Frame.pop hFf (hSf.mod.trans hsame.mod).symm ?_ ?_ ?_ ?_
      · exact (hSf.vars.trans hsame.vars).symm
      · exact hSf.scopes.trans hsame.scopes
      · intro x hx
        refine ⟨hSf.sub x ((hvis x).2 (Or.inr hx)), ?_⟩
        obtain ⟨lv, si', v, h1, h2, _⟩ := hF.vis x hx
        exact ⟨lv, h1, lookup_key h2⟩
      · intro r hr
        rcases hdom r hr with h0 | h0
        · exact Or.inr (fun a si' x e => by subst e; exact hF.inv.fresh _ _ _ h0)
        · exact Or.inl h0
    · refine ext_block hF.inv (hleb.trans hXf.le) (Nat.le_trans (Nat.le_succ _) hXf.next) ?_ ?_ hdom
      · intro r v hv hr hn hd
        refine hXf.keep r v (hkeepb r v hv) hr ?_ hd
        intro a si' x e hmem
        rcases List.mem_cons.1 hmem with e' | e'
        · subst e; subst e'
          exact absurd (hF.inv.fresh _ _ _ (by rw [hv]; simp)) (Nat.lt_irrefl _)
        · exact hn a si' x e e'
      · intro r v hv hr hn hd
        have h1 := hXf.back r v hv hr (fun a si' x e hmem => hn a si' x e hmem) hd
        rcases hbackb r v h1 with h2 | ⟨x, _, rfl⟩
        · exact h2
        · exact absurd List.mem_cons_self (hn _ _ _ rfl)
  refine Sat.bind (ih.stmts W tenv1 tenv2 { penv with scopes := sc :: penv.scopes }
    { env with scopes := (sc, s.nextScope) :: env.scopes } _ sc stmts tn1 tn2 rst1 rst2 lo hp hF1
    (by rw [hsame.scopes]; rfl) hTop hlo hts hrs hE2) ?_
  rintro fl s1 ⟨⟨tenv'', hS'', hF'', hnorm⟩, hXS, hT1, hfl⟩
  cases fl with
  | normal v =>
    obtain ⟨rfl, hdv⟩ := hfl
    have htt := hnorm _ rfl
    subst htt
    cases value with
    | none =>
      obtain ⟨rfl, rfl⟩ := hrv
      subst htv
      simp only [m_pure_bind, sat_release_bind, sat_pure]
      obtain ⟨g1, g2⟩ := exit s1 _ hF'' hS'' hXS
      exact ⟨g1, g2, rfl, fun r hr => hr.elim, hdv⟩
    | some e =>
      simp only [m_bind_assoc, m_pure_bind]
      refine Sat.bind (ih.expr W _ { penv with scopes := sc :: penv.scopes }
        { env with scopes := (sc, s.nextScope) :: env.scopes } s1 e tn2 tn3 ty rst2 rst3 rho hp hF''
        htv hrv hE) ?_
      rintro v' s2 ⟨hF2, hX2, hv2, hg2⟩
      simp only [sat_release_bind, sat_pure]
      obtain ⟨g1, g2⟩ := exit s2 _ hF2 hS'' (hXS.trans hX2.toS)
      have hT2 := hT1.ext hX2.dom (rpExpr_mono hrv).1
      have hsurv : ∀ r, Targets v' r →
          ¬ ScopeRoots env.vars env.act sc s.nextScope r ∧ Gam env W.P rho r := by
        intro r hr
        obtain ⟨q, hq, hrq⟩ := hg2 r hr
        cases q with
        | «local» y =>
          obtain ⟨ly, siy, k1, k2, rfl⟩ := hrq
          have k2' : ((sc, s.nextScope) :: env.scopes).lookup ly.scope = some siy := k2
          rw [lookup_cons] at k2'
          by_cases e : ly.scope = sc
          · simp only [e, if_true, Option.some.injEq] at k2'
            subst k2'
            rcases hasTy_target_dom hv2 hr with ⟨g, hg'⟩ | hd
            · cases hg'
            · exact absurd (hT2 _ _ _ rfl y hd) (hkeep y hq)
          · simp only [e, if_false] at k2'
            refine ⟨?_, ⟨.local y, hq, ly, siy, k1, k2', rfl⟩⟩
            rintro ⟨x', lv', _, _, e'⟩
            cases e'
            exact absurd (hF.inst_lt k2').2 (Nat.lt_irrefl _)
        | global g =>
          have hrq' : r = RootInst.global g := hrq
          subst hrq'
          exact ⟨(by rintro ⟨_, _, _, _, e⟩; cases e), ⟨.global g, hq, rfl⟩⟩
        | param j =>
          refine ⟨?_, ⟨.param j, hq, hrq⟩⟩
          rintro ⟨x', lv', _, _, rfl⟩
          exact absurd (Nat.lt_of_lt_of_le (hF.pAge j _ _ _ hrq) hF.base_le) (Nat.lt_irrefl _)
      obtain ⟨hagree, _⟩ := releaseScope_roots env.vars env.act sc s.nextScope s2.store
      exact ⟨g1, g2, hv2.agree hagree (fun r hr => (hsurv r hr).1), fun r hr => (hsurv r hr).2, hdv⟩
  | brk =>
    obtain ⟨g1, g2⟩ := exit s1 _ hF'' hS'' hXS
    cases value <;> simp only [m_pure_bind, sat_release_bind, sat_pure] <;>
      exact ⟨g1, g2, by rw [← hsame.loops]; exact hfl.1, hfl.2⟩
  | cont =>
    obtain ⟨g1, g2⟩ := exit s1 _ hF'' hS'' hXS
    cases value <;> simp only [m_pure_bind, sat_release_bind, sat_pure] <;>
      exact ⟨g1, g2, by rw [← hsame.loops]; exact hfl⟩
  | ret v =>
    obtain ⟨g1, g2⟩ := exit s1 _ hF'' hS'' hXS
    have hret : RetOk m W tenv penv (relSt env sc s.nextScope s1) v :=
      RetOk.release hF (Nat.le_trans (Nat.le_succ _) hXS.next) hF.base_le
        (hfl.2.tsame hsame.impl rfl)
    cases value <;> simp only [m_pure_bind, sat_release_bind, sat_pure] <;>
      exact ⟨g1, g2, by rw [← hsame.inExpr]; exact hfl.1, hret⟩

end Goose.Core.Sound

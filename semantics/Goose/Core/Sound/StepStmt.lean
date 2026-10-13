import Goose.Core.Sound.StepUse

/-!
One step of the induction on fuel for the statements that bind, write, rebind
and grow.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {n : Nat}

set_option maxHeartbeats 1600000 in
theorem step_stmt_a (ih : Specs m prof n) :
    ∀ (W : World) (tenv tenv' : TEnv) (penv : PEnv) (env : Env) (s : St) (sc : Nat) (st : Stmt)
    (tn tn' : Nat) (rst rst' : RState) (lo : Nat),
    (match st with
      | .letS .. | .assign .. | .assignOp .. | .rebind .. | .expr .. | .append .. => True
      | _ => False) →
    Perm m W → Frame m W tenv penv env s → tenv.scopes.head? = some sc → TopB env lo rst.nextVar s →
    lo ≤ rst.nextVar →
    tyStmt tenv sc st tn = .ok (tenv', tn') → rpStmt penv st rst = .ok ((), rst') →
    EffLe rst'.eff W.E →
    Sat (execStmt (n + 1) ⟨prof, m⟩ env st) s (fun fl s' =>
      Frame m W tenv' penv env s' ∧ TSame tenv tenv' ∧ ExtS env (Dset W) s s' ∧ TopB env lo rst'.nextVar s' ∧
      match fl with
      | .normal _ => st.diverges m.noReturn = false
      | .brk => tenv.loops ≠ 0 ∧ st.hasBreak = true
      | .cont => tenv.loops ≠ 0
      | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v) := by
  intro W tenv tenv' penv env s sc st tn tn' rst rst' lo hsel hp hF hsc hT hlo ht hr hE
  have hcur := (rpStmt_mono hr).1
  cases st with
  | letS x e o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, lv, t1, hd, te, t2, hte, heq, rfl, rfl⟩ := ht
    obtain ⟨hxn, re, r1, hre, hr⟩ := hr
    obtain ⟨hxt, hlv, hlsc, hst, _⟩ := declare_ok _ _ _ _ _ hd
    simp only at hlv hlsc hst
    rw [hF.vars_t] at hlv
    obtain ⟨si, rest, htop, hlk⟩ := hF.top hsc
    have hpv : penv.impl.vars[x]? = some lv := by rw [hF.vars_p]; exact hlv
    have hmono1 := rpExpr_mono hre
    have hb : rst' = r1 ∧ (lv.ty.isRefLike = true → bindRootsV penv penv.scopes x re = .ok ()) := by
      simp only [hpv] at hr
      by_cases hrl : lv.ty.isRefLike = true
      · simp only [hrl, if_true] at hr; inv at hr; exact ⟨hr.2, fun _ => hr.1⟩
      · simp only [hrl] at hr; inv at hr; exact ⟨hr, fun h => absurd h hrl⟩
    obtain ⟨rfl, hbr⟩ := hb
    simp only [execStmt]
    refine Sat.bind (ih.expr W tenv penv env s e _ _ _ _ _ _ hp hF hte hre hE) ?_
    rintro v s1 ⟨hF1, hX1, hv0, hg⟩
    have hv := hasTy_passable hv0 heq
    have hlk' : env.scopes.lookup lv.scope = some si := hlsc ▸ hlk
    simp only [rootOf, hlv, hlk', sat_pure_bind, sat_bindRoot_bind, sat_pure]
    have hfree0 : s.store.roots[RootInst.local env.act si x]? = none := by
      cases h0 : s.store.roots[RootInst.local env.act si x]? with
      | none => rfl
      | some v0 =>
        have := (hT _ _ _ htop x (by rw [h0]; simp)).2
        rw [hxn] at this
        exact absurd this (Nat.lt_irrefl _)
    have hfree : s1.store.roots[RootInst.local env.act si x]? = none := by
      cases h1 : s1.store.roots[RootInst.local env.act si x]? with
      | none => rfl
      | some v1 => exact absurd hfree0 (hX1.dom _ (by rw [h1]; simp))
    have hroot : ∀ r, Targets v r → (∃ ann, penv.ann x = some ann ∧ Gam env W.P ann r) ∧
        Older r (.local env.act si x) := by
      by_cases hrl : lv.ty.isRefLike = true
      · exact bind_roots_sem hF1 (hbr hrl) hlv hlk' hg
      · exact hasTy_no_targets hv (by simpa using hrl)
    have htop' : env.scopes = (lv.scope, si) :: rest := hlsc ▸ htop
    refine ⟨hF1.bind hlv hlk' (paramOk_of_storable hst) hfree hv hroot, TSame.cons _ _,
      hX1.toS.trans (extS_bind htop' hlv hfree), ?_, rfl⟩
    refine topB_bind htop (hT.ext hX1.dom (Nat.le_refl _)) ?_ ?_ ?_
    · rw [hxn]; exact hlo
    · rw [hxn]; exact hmono1.1
    · exact Nat.le_trans (Nat.le_succ _) hmono1.1
  | assign p e o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, t, b, t1, htp, hfl, te, t2, hte, heq, _, rfl, rfl⟩ := ht
    obtain ⟨rp, r1, hrp, re, r2, hre, hck, r3, hw, rfl⟩ := hr
    have : te = t := by simpa using heq
    subst this
    obtain ⟨_, hin0⟩ := addWrites_ok _ _ _ hw
    have hE3 : EffLe r3.eff W.E :=
      EffLe.trans ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun h => h⟩ hE
    have hin : ∀ t', t' ∈ rootsTargets rp → t' ∈ W.E.writes := fun t' ht' => hE3.2.1 t' (hin0 t' ht')
    have hE2 : EffLe r2.eff W.E := (PMono.addWrites _ _ _ _ hw).2.trans hE3
    simp only [execStmt]
    refine Sat.bind (ih.place W tenv' penv env s p _ _ _ _ _ _ _ hp hF htp hrp
      ((rpExpr_mono hre).2.trans hE2)) ?_
    rintro l s1 ⟨hF1, hX1, hpl, hg⟩
    refine Sat.bind (ih.expr W tenv' penv env s1 e _ _ _ _ _ _ hp hF1 hte hre hE2) ?_
    rintro v s2 ⟨hF2, hX2, hv, hgv⟩
    rcases hpl with ⟨hrt, hl⟩ | ⟨x, lv, si, v', hpv, _, _, _, _, hrl, _⟩ |
      ⟨x, lv, mu0, mus, E, ann, rfl, hlv, hty, rfl, hflE, hpath, hann, hgl, hlive⟩
    · have hfl' : te.flat = true := by
        cases hf : te.flat with
        | true => rfl
        | false =>
          simp only [hf, Bool.false_or, Bool.and_eq_true] at hfl
          rw [isSlice_not_refTarget hfl.1] at hrt; cases hrt
      have hlt := access hp (hl.mono hX2.le) hg (fun t' ht' => Or.inr (Or.inl (hin t' ht')))
      refine sat_writeLoc_bind hlt (fun st' hw' => ?_)
      simp only [sat_pure]
      have hstep := write_flatStep _ _ _ _ _ hfl' hlt (hv.flat hfl') hw'
      have hX := (hX1.trans hX2).trans (Ext.of_flatStep hstep)
      exact ⟨hF2.flatStep hstep, TSame.refl _, hX.toS, hT.ext hX.dom hcur, rfl⟩
    · subst hpv
      cases hf : te.flat with
      | true => rw [refTarget_not_refLike (flat_refTarget hf)] at hrl; cases hrl
      | false => simp [hf, Place.derefVar?] at hfl
    · -- A slice stored through a reference to a slice variable of a caller.
      have hsv : penv.isRefSliceVar x = true := by
        simp [PEnv.isRefSliceVar, hF2.vars_p, hlv, hty, Ty.isRefSlice, hflE]
      obtain ⟨cont, hc, hsub⟩ := checkStore_ok _ _ _ hck x rfl hsv
      obtain ⟨hnl, hann', hpr⟩ := hF2.pref x _ hc
      rw [hann] at hann'
      cases hann'
      obtain ⟨q, hq, hrq⟩ := hgl
      simp only [List.mem_singleton] at hq
      subst hq
      obtain ⟨hD, _, hFW⟩ := hpr lv mu0 mus E hlv hty _ hrq
      obtain ⟨old, ho, _, _⟩ := hF2.sa _ E hD
      have hl : l = ⟨l.root, []⟩ := by
        cases l; simp only at hpath; simp [hpath]
      rw [hl]
      refine sat_writeRoot_bind ho ?_
      simp only [sat_pure]
      obtain ⟨hFw, hXw⟩ := hF2.outwrite hD (hasTy_slice_mu hv)
        (fun t ht' => hFW t (gam_noEnv ((hgv t ht').subset hsub) hnl))
      have hX := (hX1.trans hX2).trans hXw
      exact ⟨hFw, TSame.refl _, hX.toS, hT.ext hX.dom hcur, rfl⟩
  | assignOp op p e o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, t, b, t1, htp, it, rfl, te, t2, hte, iu, rfl, rfl, _, rfl, rfl⟩ := ht
    obtain ⟨rp, r1, hrp, re, r2, hre, r3, hrd, r4, hwr, hfin⟩ := hr
    have hE4 : EffLe r4.eff W.E := by
      refine EffLe.trans ?_ hE
      rcases hfin with ⟨_, hna⟩ | ⟨_, rfl⟩
      · exact (PMono.noteAborts _ _ _ hna).2
      · exact EffLe.refl _
    obtain ⟨_, hinr⟩ := addReads_ok _ _ _ hrd
    have hE3 := (PMono.addWrites _ _ _ _ hwr).2.trans hE4
    have hE2 := (PMono.addReads _ _ _ _ hrd).2.trans hE3
    simp only [execStmt]
    refine Sat.bind (ih.place W tenv' penv env s p _ _ _ _ _ _ _ hp hF htp hrp
      ((rpExpr_mono hre).2.trans hE2)) ?_
    rintro l s1 ⟨hF1, hX1, hpl, hg⟩
    rcases hpl with ⟨_, hl⟩ | ⟨x, lv, si, v', _, _, _, _, _, hrl, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, h3, _⟩
    case inr.inr => cases h3
    · have hlt := access hp hl hg (fun t' ht' => Or.inl (hE3.1 t' (hinr t' ht')))
      refine sat_readLoc_bind hlt (fun v0 _ hT0 => ?_)
      cases v0 <;> simp only [FlatTy] at hT0
      subst hT0
      simp only [expectInt, sat_pure_bind]
      refine Sat.bind (ih.expr W tenv' penv env s1 e _ _ _ _ _ _ hp hF1 hte hre hE2) ?_
      rintro v s2 ⟨hF2, hX2, hv, _⟩
      obtain ⟨y, rfl⟩ := hasTy_int hv
      simp only [expectInt, sat_pure_bind, expectSameTy, if_true]
      split
      · have hlt2 := LocTy.mono hX2.le hlt
        refine sat_writeLoc_bind hlt2 (fun st' hw' => ?_)
        simp only [sat_pure]
        have hstep := write_flatStep _ _ _ _ (.int it) rfl hlt2
          (show FlatTy (.int it) (Val.int it _) from rfl) hw'
        have hX := (hX1.trans hX2).trans (Ext.of_flatStep hstep)
        exact ⟨hF2.flatStep hstep, TSame.refl _, hX.toS, hT.ext hX.dom hcur, rfl⟩
      · trivial
    · simp [Ty.isRefLike] at hrl
  | rebind x e o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, hx, lv, hlv, hrl, _, te, t1, hte, heq, rfl, rfl⟩ := ht
    obtain ⟨re, r1, hre, hb, hfin⟩ := hr
    have hE1 : EffLe r1.eff W.E := by
      refine EffLe.trans ?_ hE
      rcases hfin with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun h => h⟩
      · exact EffLe.refl _
    simp only [execStmt]
    refine Sat.bind (ih.expr W tenv' penv env s e _ _ _ _ _ _ hp hF hte hre hE1) ?_
    rintro v s1 ⟨hF1, hX1, hv0, hg⟩
    have hv := hasTy_passable hv0 heq
    obtain ⟨lv1, si, old, h1, h2, h3, h4, h5⟩ := hF1.vis x hx
    rw [hF.vars_t, h1] at hlv
    cases hlv
    simp only [rootOf, h1, h2, sat_pure_bind]
    refine sat_writeRoot_bind h4 ?_
    simp only [sat_pure]
    have hold := isRef_of_refLike h5 hrl
    have hroot := bind_roots_sem hF1 hb h1 h2 hg
    have hX := hX1.trans (ext_rebind (v := v) (lookup_inst h2) h4 hold)
    exact ⟨hF1.rebind h1 h2 h4 hold hv hroot, TSame.refl _, hX.toS, hT.ext hX.dom hcur, rfl⟩
  | expr e o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, te, t1, hte, rfl, rfl⟩ := ht
    obtain ⟨re, hre⟩ := hr
    simp only [execStmt]
    refine Sat.bind_eq (ih.expr W tenv' penv env s e _ _ _ _ _ _ hp hF hte hre hE) ?_
    rintro v s1 heq ⟨hF1, hX1, _, _⟩
    simp only [sat_pure]
    refine ⟨hF1, TSame.refl _, hX1.toS, hT.ext hX1.dom hcur, ?_⟩
    -- A call that returned is not a call of a function that never returns.
    cases hdv : (Stmt.expr e o).diverges m.noReturn with
    | false => rfl
    | true =>
      exact absurd heq (never_call_expr ⟨prof, m⟩ m.noReturn (noReturn_sound m prof) n env e o
        (by cases e <;> first
              | (simp [Stmt.diverges] at hdv; done)
              | (simpa [Stmt.diverges] using hdv)) s v s1)
  | append owner src o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, t, b, t1, htp, ht⟩ := ht
    obtain ⟨rp, r1, hrp, rv, r2, hrv, r3, hrd, hgr⟩ := hr
    obtain ⟨_, hin⟩ := addGrows_ok _ _ _ hgr
    have hE3 : EffLe r3.eff W.E := (PMono.addGrows _ _ _ _ hgr).2.trans hE
    have hE2 := (PMono.addReads _ _ _ _ hrd).2.trans hE3
    cases t <;> inv at ht
    rename_i el
    obtain ⟨sel, b', t2, htv, heq, _, rfl, rfl⟩ := ht
    have : sel = el := by simpa using heq
    subst this
    simp only [execStmt]
    refine Sat.bind (ih.place W tenv' penv env s owner _ _ _ _ _ _ _ hp hF htp hrp
      ((rpView_mono hrv).2.trans hE2)) ?_
    rintro l s1 ⟨hF1, hX1, hpl, hg⟩
    refine Sat.bind (ih.view W tenv' penv env s1 src _ _ _ _ _ _ _ hp hF1 htv hrv hE2) ?_
    rintro vw s2 ⟨hF2, hX2, hvw, _⟩
    refine sat_readRun_bind hvw (fun vs hvs => ?_)
    rcases hpl with ⟨hrt, hl⟩ | ⟨x, lv, si, v', _, _, _, _, _, hrl, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, h3, _⟩
    case inr.inr => cases h3
    · have hlt := access hp (hl.mono hX2.le) hg
        (fun t' ht' => Or.inr (Or.inr (hE.2.2.1 t' (hin t' ht'))))
      refine sat_appendLoc_bind hlt (fun st' i happ => ?_)
      simp only [sat_pure]
      have hstep := append_flatStep _ _ _ _ _ _ hlt hvs happ
      have hX := (hX1.trans hX2).trans (Ext.of_flatStep hstep)
      exact ⟨hF2.flatStep hstep, TSame.refl _, hX.toS, hT.ext hX.dom hcur, rfl⟩
    · simp [Ty.isRefLike] at hrl
  | _ => exact hsel.elim

end Goose.Core.Sound

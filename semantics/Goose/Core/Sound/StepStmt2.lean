import Goose.Core.Sound.StepUse

/-!
One step of the induction on fuel for the control statements.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {n : Nat}

set_option maxHeartbeats 1600000 in
theorem step_stmt_b (ih : Specs m prof n) :
    ∀ (W : World) (tenv tenv' : TEnv) (penv : PEnv) (env : Env) (s : St) (sc : Nat) (st : Stmt)
    (tn tn' : Nat) (rst rst' : RState) (lo : Nat),
    (match st with
      | .letS .. | .assign .. | .assignOp .. | .rebind .. | .expr .. | .append .. => False
      | _ => True) →
    Perm m W → Frame m W tenv penv env s → tenv.scopes.head? = some sc → TopB env lo rst.nextVar s →
    lo ≤ rst.nextVar →
    tyStmt tenv sc st tn = .ok (tenv', tn') → rpStmt penv st rst = .ok ((), rst') →
    EffLe rst'.eff W.E →
    Sat (execStmt (n + 1) ⟨prof, m⟩ env st) s (fun fl s' =>
      Frame m W tenv' penv env s' ∧ TSame tenv tenv' ∧ ExtS env (Dset W) s s' ∧ TopB env lo rst'.nextVar s' ∧
      match fl with
      | .normal _ => st.diverges = false
      | .brk => tenv.loops ≠ 0 ∧ st.hasBreak = true
      | .cont => tenv.loops ≠ 0
      | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v) := by
  intro W tenv tenv' penv env s sc st tn tn' rst rst' lo hsel hp hF hsc hT hlo ht hr hE
  have hcur := (rpStmt_mono hr).1
  cases st with
  | ifS c t f o =>
    cases f with
    | none =>
      simp only [tyStmt] at ht; inv at ht
      simp only [rpStmt] at hr; inv at hr
      obtain ⟨_, tc, t1, htc, rfl, tt, t2, htt, rfl, rfl⟩ := ht
      obtain ⟨rc, r1, hrc, rt, l1, l2, hrt⟩ := hr
      simp only [execStmt]
      refine Sat.bind (ih.expr W tenv' penv env s c _ _ _ _ _ _ hp hF htc hrc
        ((rpBlockValue_mono hrt).2.trans hE)) ?_
      rintro vc s1 ⟨hF1, hX1, hv, _⟩
      obtain ⟨x, rfl⟩ := hasTy_bool hv
      simp only [expectBool, sat_pure_bind]
      cases x
      · simp only [Bool.false_eq_true, if_false, sat_pure_bind, sat_pure]
        exact ⟨hF1, TSame.refl _, hX1.toS, hT.ext hX1.dom hcur, rfl⟩
      · simp only [if_true]
        refine Sat.bind (block_of_checks ih.block hp hF1 t [] [] htt hrt hE rfl rfl
          (fun k x v ty' h => by simp at h)) ?_
        rintro fl s2 ⟨hF2, hX2, hfl⟩
        have hX := hX1.trans hX2
        cases fl with
        | normal v =>
          simp only [sat_pure]
          exact ⟨hF2, TSame.refl _, hX.toS, hT.ext hX.dom hcur, rfl⟩
        | brk =>
          simp only [sat_pure]
          exact ⟨hF2, TSame.refl _, hX.toS, hT.ext hX.dom hcur, hfl.1, by simp [Stmt.hasBreak, hfl.2]⟩
        | cont =>
          simp only [sat_pure]
          exact ⟨hF2, TSame.refl _, hX.toS, hT.ext hX.dom hcur, hfl⟩
        | ret v =>
          simp only [sat_pure]
          exact ⟨hF2, TSame.refl _, hX.toS, hT.ext hX.dom hcur, hfl⟩
    | some fb =>
      simp only [tyStmt] at ht; inv at ht
      simp only [rpStmt] at hr; inv at hr
      obtain ⟨_, tc, t1, htc, rfl, tt, t2, htt, ft, t3, htf, rfl, rfl⟩ := ht
      obtain ⟨rc, r1, hrc, rt, l1, l2, r2, hrt, rf, k1, k2, hrf⟩ := hr
      have hE2 := (rpBlockValue_mono hrf).2.trans hE
      simp only [execStmt]
      refine Sat.bind (ih.expr W tenv' penv env s c _ _ _ _ _ _ hp hF htc hrc
        ((rpBlockValue_mono hrt).2.trans hE2)) ?_
      rintro vc s1 ⟨hF1, hX1, hv, _⟩
      obtain ⟨x, rfl⟩ := hasTy_bool hv
      simp only [expectBool, sat_pure_bind]
      cases x
      · simp only [Bool.false_eq_true, if_false]
        refine Sat.bind (block_of_checks ih.block hp hF1 fb [] [] htf hrf hE rfl rfl
          (fun k x v ty' h => by simp at h)) ?_
        rintro fl s2 ⟨hF2, hX2, hfl⟩
        have hX := hX1.trans hX2
        cases fl with
        | normal v =>
          simp only [sat_pure]
          exact ⟨hF2, TSame.refl _, hX.toS, hT.ext hX.dom hcur, by simp [Stmt.diverges, hfl.2.2]⟩
        | brk =>
          simp only [sat_pure]
          exact ⟨hF2, TSame.refl _, hX.toS, hT.ext hX.dom hcur, hfl.1, by simp [Stmt.hasBreak, hfl.2]⟩
        | cont =>
          simp only [sat_pure]
          exact ⟨hF2, TSame.refl _, hX.toS, hT.ext hX.dom hcur, hfl⟩
        | ret v =>
          simp only [sat_pure]
          exact ⟨hF2, TSame.refl _, hX.toS, hT.ext hX.dom hcur, hfl⟩
      · simp only [if_true]
        refine Sat.bind (block_of_checks ih.block hp hF1 t [] [] htt hrt hE2 rfl rfl
          (fun k x v ty' h => by simp at h)) ?_
        rintro fl s2 ⟨hF2, hX2, hfl⟩
        have hX := hX1.trans hX2
        cases fl with
        | normal v =>
          simp only [sat_pure]
          exact ⟨hF2, TSame.refl _, hX.toS, hT.ext hX.dom hcur, by simp [Stmt.diverges, hfl.2.2]⟩
        | brk =>
          simp only [sat_pure]
          exact ⟨hF2, TSame.refl _, hX.toS, hT.ext hX.dom hcur, hfl.1, by simp [Stmt.hasBreak, hfl.2]⟩
        | cont =>
          simp only [sat_pure]
          exact ⟨hF2, TSame.refl _, hX.toS, hT.ext hX.dom hcur, hfl⟩
        | ret v =>
          simp only [sat_pure]
          exact ⟨hF2, TSame.refl _, hX.toS, hT.ext hX.dom hcur, hfl⟩
  | «while» c b o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, tc, t1, htc, rfl, bt, t2, htb, rfl, rfl⟩ := ht
    obtain ⟨rc, r1, hrc, rb, l1, l2, hrb⟩ := hr
    simp only [execStmt]
    refine (ih.while_ W tenv' penv env s c b _ _ _ _ _ _ _ _ _ _ hp hF htc htb hrc hrb hE).mono ?_
    rintro fl s1 ⟨hF1, hX1, hfl, hdv⟩
    refine ⟨hF1, TSame.refl _, hX1.toS, hT.ext hX1.dom hcur, ?_⟩
    cases fl with
    | normal v => exact while_diverges c b o (hdv v rfl)
    | brk => exact hfl.elim
    | cont => exact hfl.elim
    | ret v => exact hfl
  | forRange x lo' hi b o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, lv, t0, hd, tl, t1, htl, it, rfl, th, t2, hth, iu, rfl, rfl, hlty, bt, t3, htb, rfl,
      rfl⟩ := ht
    obtain ⟨hxn, rl, r1, hrl, rh, r2, hrh, rb, l1, l2, r3, hrb, hck, rfl⟩ := hr
    obtain ⟨_, hlv, hlsc, _, _⟩ := declare_ok _ _ _ _ _ hd
    simp only at hlv hlsc
    rw [hF.vars_t] at hlv
    have hlty' : lv.ty = .int it := by simpa using hlty
    have hrng := rpBlockValue_rng _ _ _ _ _ _ _ hrb
    simp only at hrng
    have hk0 : ∀ y, RootRef.local y ∈ rb → ¬ (x ≤ y ∧ y < r2.nextVar) := by
      intro y hy
      have := checkBlockValue_ok _ _ _ hck y hy
      rw [hxn, ← hrng]; exact this
    have hxlt : x < r2.nextVar := by
      rw [hxn]
      exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (rpExpr_mono hrl).1)
        (rpExpr_mono hrh).1
    have hE2 := (rpBlockValue_mono hrb).2.trans hE
    simp only [execStmt]
    refine Sat.bind (ih.expr W tenv' penv env s lo' _ _ _ _ _ _ hp hF htl hrl
      ((rpExpr_mono hrh).2.trans hE2)) ?_
    rintro va s1 ⟨hF1, hX1, hv, _⟩
    obtain ⟨a, rfl⟩ := hasTy_int hv
    simp only [expectInt, sat_pure_bind]
    refine Sat.bind (ih.expr W tenv' penv env s1 hi _ _ _ _ _ _ hp hF1 hth hrh hE2) ?_
    rintro vb s2 ⟨hF2, hX2, hv2, _⟩
    obtain ⟨b', rfl⟩ := hasTy_int hv2
    simp only [expectInt, sat_pure_bind, expectSameTy, if_true]
    refine (ih.range W tenv' penv env s2 x it _ _ b _ _ _ _ _ _ _ hp hF2 ⟨lv, hlv, hlsc, hlty'⟩ hxlt
      htb hrb hE hk0).mono ?_
    rintro fl s3 ⟨hF3, hX3, hfl⟩
    have hX := (hX1.trans hX2).trans hX3
    refine ⟨hF3, TSame.refl _, hX.toS, hT.ext hX.dom hcur, ?_⟩
    cases fl with
    | normal v => rfl
    | brk => exact hfl.elim
    | cont => exact hfl.elim
    | ret v => exact hfl
  | forEach x idx v byRef b o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, lv, t0, hd, t1, hdi, el, mu, t2, htv, t3, hlo, bt, t4, htb, rfl, rfl⟩ := ht
    obtain ⟨hxi, rv, r1, hrv, hr⟩ := hr
    obtain ⟨hxt, hlv, hlsc, hst, ht0⟩ := declare_ok _ _ _ _ _ hd
    simp only at hlv hlsc hst ht0
    rw [hF.vars_t] at hlv
    obtain ⟨_, hjs⟩ := declareIndex_ok _ _ _ _ _ hdi
    obtain ⟨_, hxty⟩ := loopVarOk_ok _ _ _ _ _ _ hlo
    have hxn : x = rst.nextVar := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hxi
      exact hxi.1
    have hj : ∀ j, idx = some j → j = x + 1 ∧ ∃ lj, env.vars[j]? = some lj ∧ lj.scope = b.scope ∧
        lj.ty = .int .i64 := by
      intro j e
      obtain ⟨g1, lj, g2, g3, g4⟩ := hjs j e
      rw [hF.vars_t] at g2
      exact ⟨by rw [g1, ht0, hxt], lj, g2, g3, g4⟩
    have hlt1 : x + idx.toList.length < r1.nextVar := by
      have h2 := (rpView_mono hrv).1
      rw [hxn]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right (Nat.lt_succ_self _) _) h2
    simp only [execStmt]
    rcases hr with ⟨hb1, hbr, rb, l1, l2, r2, hrb, hck, rfl⟩ | ⟨hb1, r2, hrd, rb, l1, l2, r3, hrb, hck, rfl⟩
    · subst hb1
      have hrng := rpBlockValue_rng _ _ _ _ _ _ _ hrb
      simp only at hrng
      have hk0 : ∀ y, RootRef.local y ∈ rb → ¬ (x ≤ y ∧ y < r1.nextVar) := by
        intro y hy
        have := checkBlockValue_ok _ _ _ hck y hy
        rw [hxn, ← hrng]; exact this
      refine Sat.bind (ih.view W tenv' penv env s v _ _ _ _ _ _ _ hp hF htv hrv
        ((rpBlockValue_mono hrb).2.trans hE)) ?_
      rintro vw s1 ⟨hF1, hX1, hvw, hg⟩
      refine (ih.each W tenv' penv env s1 x idx true b vw 0 el rv _ _ _ _ _ _ _ hp hF1 hvw hg
        ⟨lv, hlv, hlsc, hst, by rw [if_pos rfl]; exact ⟨by simpa using hxty, hbr⟩⟩ hj hlt1 htb hrb hE
        hk0).mono ?_
      rintro fl s3 ⟨hF3, hX3, hfl⟩
      have hX := hX1.trans hX3
      refine ⟨hF3, TSame.refl _, hX.toS, hT.ext hX.dom hcur, ?_⟩
      cases fl with
      | normal v => rfl
      | brk => exact hfl.elim
      | cont => exact hfl.elim
      | ret v => exact hfl
    · have hbf : byRef = false := by simpa using hb1
      subst hbf
      have hrng := rpBlockValue_rng _ _ _ _ _ _ _ hrb
      simp only at hrng
      have hnv := (addReads_ok _ _ _ hrd).1
      simp only at hnv
      have hk0 : ∀ y, RootRef.local y ∈ rb → ¬ (x ≤ y ∧ y < r2.nextVar) := by
        intro y hy
        have := checkBlockValue_ok _ _ _ hck y hy
        rw [hxn, ← hrng]; exact this
      refine Sat.bind (ih.view W tenv' penv env s v _ _ _ _ _ _ _ hp hF htv hrv
        ((PMono.addReads _ _ _ _ hrd).2.trans ((rpBlockValue_mono hrb).2.trans hE))) ?_
      rintro vw s1 ⟨hF1, hX1, hvw, hg⟩
      refine (ih.each W tenv' penv env s1 x idx false b vw 0 el rv _ _ _ _ _ _ _ hp hF1 hvw hg
        ⟨lv, hlv, hlsc, hst, by simpa using hxty⟩ hj (by rw [hnv]; exact hlt1) htb hrb hE hk0).mono ?_
      rintro fl s3 ⟨hF3, hX3, hfl⟩
      have hX := hX1.trans hX3
      refine ⟨hF3, TSame.refl _, hX.toS, hT.ext hX.dom hcur, ?_⟩
      cases fl with
      | normal v => rfl
      | brk => exact hfl.elim
      | cont => exact hfl.elim
      | ret v => exact hfl
  | ret e o =>
    cases e with
    | none =>
      simp only [tyStmt] at ht; inv at ht
      simp only [rpStmt] at hr; inv at hr
      obtain ⟨_, t1, hru, rfl, rfl⟩ := ht
      subst hr
      obtain ⟨_, hne', impl, himpl, hres⟩ := retUnit_ok _ _ _ hru
      simp only [execStmt, sat_pure]
      exact ⟨hF, TSame.refl _, (Ext.refl _ _ _).toS, hT.ext (fun _ h => h) hcur, hne',
        impl, himpl, Or.inl ⟨hres, rfl⟩, fun r hr' => hr'.elim⟩
    | some e' =>
      simp only [tyStmt] at ht; inv at ht
      simp only [rpStmt] at hr; inv at hr
      obtain ⟨_, t, t0, hrt, te, t1, hte, heq, rfl, rfl⟩ := ht
      obtain ⟨rho, r1, hre, hck, rfl⟩ := hr
      obtain ⟨ht0, hne', impl, himpl, hres⟩ := retTy_ok _ _ _ hrt
      simp only at ht0 hres
      subst ht0
      obtain ⟨hnl, declared, hd, hsub⟩ := checkResultV_ok _ _ hck
      simp only [execStmt]
      refine Sat.bind (ih.expr W tenv' penv env s e' _ _ _ _ _ _ hp hF hte hre hE) ?_
      rintro v s1 ⟨hF1, hX1, hv0, hg⟩
      have hv := hasTy_passable hv0 heq
      simp only [sat_pure]
      exact ⟨hF1, TSame.refl _, hX1.toS, hT.ext hX1.dom hcur, hne',
        impl, himpl, Or.inr ⟨_, hres, hv⟩,
        fun r hr' => ⟨declared, hd, (gam_noEnv (hg r hr') hnl).subset hsub⟩⟩
  | brk o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, hl, rfl, rfl⟩ := ht
    subst hr
    simp only [execStmt, sat_pure]
    exact ⟨hF, TSame.refl _, (Ext.refl _ _ _).toS, hT.ext (fun _ h => h) hcur, hl, rfl⟩
  | cont o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, hl, rfl, rfl⟩ := ht
    subst hr
    simp only [execStmt, sat_pure]
    exact ⟨hF, TSame.refl _, (Ext.refl _ _ _).toS, hT.ext (fun _ h => h) hcur, hl⟩
  | print args o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, t1, htp, rfl, rfl⟩ := ht
    obtain ⟨r1, hrp, hno⟩ := hr
    simp only [execStmt]
    refine Sat.bind (printArgs_spec ih.printArg hp args s _ _ _ _ hF htp hrp
      ((PMono.noteOutputs _ _ _ hno).2.trans hE)) ?_
    rintro parts s1 ⟨hF1, hX1⟩
    simp only [sat_emit_bind, sat_pure]
    have hX := hX1.trans (Ext.of_eq (s' := { s1 with trace := s1.trace ++ (String.join parts ++ "\n") })
      rfl rfl)
    exact ⟨hF1.of_eq rfl rfl, TSame.refl _, hX.toS, hT.ext hX.dom hcur, rfl⟩
  | assertS e o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, te, t1, hte, rfl, rfl, rfl⟩ := ht
    obtain ⟨re, r1, hre, hna⟩ := hr
    simp only [execStmt]
    refine Sat.bind (ih.expr W tenv' penv env s e _ _ _ _ _ _ hp hF hte hre
      ((PMono.noteAborts _ _ _ hna).2.trans hE)) ?_
    rintro v s1 ⟨hF1, hX1, hv, _⟩
    obtain ⟨x, rfl⟩ := hasTy_bool hv
    simp only [expectBool, sat_pure_bind]
    cases x
    · simp only [Bool.false_eq_true, if_false, sat_abort]
    · simp only [if_true, sat_pure]
      exact ⟨hF1, TSame.refl _, hX1.toS, hT.ext hX1.dom hcur, rfl⟩
  | abort msg o =>
    simp only [execStmt, sat_abort]
  | exit e o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, te, t1, hte, it, rfl, rfl, rfl⟩ := ht
    obtain ⟨re, r1, hre, hna⟩ := hr
    simp only [execStmt]
    refine Sat.bind (ih.expr W tenv' penv env s e _ _ _ _ _ _ hp hF hte hre
      ((PMono.noteAborts _ _ _ hna).2.trans hE)) ?_
    rintro v s1 ⟨hF1, hX1, hv, _⟩
    obtain ⟨k, rfl⟩ := hasTy_int hv
    simp only [expectInt, sat_pure_bind, sat_stop_exit]
  | _ => exact hsel.elim

end Goose.Core.Sound

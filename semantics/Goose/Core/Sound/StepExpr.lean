import Goose.Core.Sound.StepAux

/-!
One step of the induction on fuel for expressions.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {n : Nat}

theorem noTargets_int {t : IntTy} {x : Int} {P : RootInst → Prop} : ∀ r, Targets (.int t x) r → P r :=
  fun _ h => h.elim

theorem noTargets_bool {b : Bool} {P : RootInst → Prop} : ∀ r, Targets (.bool b) r → P r :=
  fun _ h => h.elim

set_option maxHeartbeats 800000 in
theorem step_expr_a (ih : Specs m prof n) :
    ∀ (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (e : Expr) (tn tn' : Nat) (ty : Ty)
    (rst rst' : RState) (rho : List RootRef),
    (match e with
      | .lit .. | .bool .. | .not .. | .and .. | .or .. | .un .. | .bin .. | .cmp .. | .conv .. => True
      | _ => False) →
    Perm m W → Frame m W tenv penv env s →
    tyExpr tenv e tn = .ok (ty, tn') → rpExpr penv e rst = .ok (rho, rst') → EffLe rst'.eff W.E →
    Sat (evalExpr (n + 1) ⟨prof, m⟩ env e) s (fun v s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) (Dset W) s s' ∧ HasTy m W.G s'.store v ty ∧
      ∀ r, Targets v r → Gam env W.P rho r) := by
  intro W tenv penv env s e tn tn' ty rst rst' rho hsel hp hF ht hr hE
  cases e with
  | lit t v =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨_, rfl, rfl⟩ := ht
    obtain ⟨rfl, rfl⟩ := hr
    simp only [evalExpr, sat_pure]
    exact ⟨hF, Ext.refl _ _ _, rfl, noTargets_int⟩
  | bool b =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨rfl, rfl⟩ := ht
    obtain ⟨rfl, rfl⟩ := hr
    simp only [evalExpr, sat_pure]
    exact ⟨hF, Ext.refl _ _ _, trivial, noTargets_bool⟩
  | not a =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨ta, t1, hta, rfl, rfl, rfl⟩ := ht
    obtain ⟨ra, r1, hra, rfl, rfl⟩ := hr
    simp only [evalExpr]
    refine Sat.bind (ih.expr W tenv penv env s a _ _ _ _ _ _ hp hF hta hra hE) ?_
    rintro va s1 ⟨hF1, hX1, hv, _⟩
    obtain ⟨b, rfl⟩ := hasTy_bool hv
    simp only [expectBool, sat_pure_bind, sat_pure]
    exact ⟨hF1, hX1, trivial, noTargets_bool⟩
  | and a b =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨ta, t1, hta, rfl, tb, t2, htb, rfl, rfl, rfl⟩ := ht
    obtain ⟨ra, r1, hra, rb, r2, hrb, rfl, rfl⟩ := hr
    simp only [evalExpr]
    refine Sat.bind (ih.expr W tenv penv env s a _ _ _ _ _ _ hp hF hta hra
      ((rpExpr_mono hrb).2.trans hE)) ?_
    rintro va s1 ⟨hF1, hX1, hv, _⟩
    obtain ⟨x, rfl⟩ := hasTy_bool hv
    simp only [expectBool, sat_pure_bind]
    cases x
    · simp only [Bool.false_eq_true, if_false, sat_pure]
      exact ⟨hF1, hX1, trivial, noTargets_bool⟩
    · simp only [if_true]
      refine Sat.bind (ih.expr W tenv penv env s1 b _ _ _ _ _ _ hp hF1 htb hrb hE) ?_
      rintro vb s2 ⟨hF2, hX2, hv2, _⟩
      obtain ⟨y, rfl⟩ := hasTy_bool hv2
      simp only [expectBool, sat_pure_bind, sat_pure]
      exact ⟨hF2, hX1.trans hX2, trivial, noTargets_bool⟩
  | or a b =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨ta, t1, hta, rfl, tb, t2, htb, rfl, rfl, rfl⟩ := ht
    obtain ⟨ra, r1, hra, rb, r2, hrb, rfl, rfl⟩ := hr
    simp only [evalExpr]
    refine Sat.bind (ih.expr W tenv penv env s a _ _ _ _ _ _ hp hF hta hra
      ((rpExpr_mono hrb).2.trans hE)) ?_
    rintro va s1 ⟨hF1, hX1, hv, _⟩
    obtain ⟨x, rfl⟩ := hasTy_bool hv
    simp only [expectBool, sat_pure_bind]
    cases x
    · simp only [Bool.false_eq_true, if_false]
      refine Sat.bind (ih.expr W tenv penv env s1 b _ _ _ _ _ _ hp hF1 htb hrb hE) ?_
      rintro vb s2 ⟨hF2, hX2, hv2, _⟩
      obtain ⟨y, rfl⟩ := hasTy_bool hv2
      simp only [expectBool, sat_pure_bind, sat_pure]
      exact ⟨hF2, hX1.trans hX2, trivial, noTargets_bool⟩
    · simp only [if_true, sat_pure]
      exact ⟨hF1, hX1, trivial, noTargets_bool⟩
  | un op a o =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨_, ta, t1, hta, t, rfl, ht⟩ := ht
    obtain ⟨ra, r1, hra, hr⟩ := hr
    have hty : ty = .int t := by cases op <;> inv at ht <;> first | exact ht.1 | exact ht.2.1
    have hE1 : EffLe r1.eff W.E := by
      refine EffLe.trans ?_ hE
      cases op <;> inv at hr
      · obtain ⟨s2, h2, _, rfl⟩ := hr; exact (PMono.noteAborts _ _ _ h2).2
      · obtain ⟨_, rfl⟩ := hr; exact EffLe.refl _
    subst hty
    simp only [evalExpr]
    refine Sat.bind (ih.expr W tenv penv env s a _ _ _ _ _ _ hp hF hta hra hE1) ?_
    rintro va s1 ⟨hF1, hX1, hv, _⟩
    obtain ⟨x, rfl⟩ := hasTy_int hv
    simp only [expectInt, sat_pure_bind]
    split
    · exact ⟨hF1, hX1, rfl, noTargets_int⟩
    · trivial
  | bin op a b o =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨_, ta, t1, hta, t, rfl, tb, t2, htb, u, rfl, rfl, rfl, rfl⟩ := ht
    obtain ⟨ra, r1, hra, rb, r2, hrb, hr⟩ := hr
    have hE2 : EffLe r2.eff W.E := by
      refine EffLe.trans ?_ hE
      rcases hr with ⟨_, s3, h3, _, rfl⟩ | ⟨_, _, rfl⟩
      · exact (PMono.noteAborts _ _ _ h3).2
      · exact EffLe.refl _
    simp only [evalExpr]
    refine Sat.bind (ih.expr W tenv penv env s a _ _ _ _ _ _ hp hF hta hra
      ((rpExpr_mono hrb).2.trans hE2)) ?_
    rintro va s1 ⟨hF1, hX1, hv, _⟩
    obtain ⟨x, rfl⟩ := hasTy_int hv
    simp only [expectInt, sat_pure_bind]
    refine Sat.bind (ih.expr W tenv penv env s1 b _ _ _ _ _ _ hp hF1 htb hrb hE2) ?_
    rintro vb s2 ⟨hF2, hX2, hv2, _⟩
    obtain ⟨y, rfl⟩ := hasTy_int hv2
    simp only [expectInt, sat_pure_bind, expectSameTy, if_true]
    split
    · exact ⟨hF2, hX1.trans hX2, rfl, noTargets_int⟩
    · trivial
  | cmp op a b =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨ta, t1, hta, tb, t2, htb, ht⟩ := ht
    obtain ⟨ra, r1, hra, rb, r2, hrb, rfl, rfl⟩ := hr
    simp only [evalExpr]
    refine Sat.bind (ih.expr W tenv penv env s a _ _ _ _ _ _ hp hF hta hra
      ((rpExpr_mono hrb).2.trans hE)) ?_
    rintro va s1 ⟨hF1, hX1, hv, _⟩
    refine Sat.bind (ih.expr W tenv penv env s1 b _ _ _ _ _ _ hp hF1 htb hrb hE) ?_
    rintro vb s2 ⟨hF2, hX2, hv2, _⟩
    have hv' := hv.mono hX2.le
    cases ta <;> cases tb <;> inv at ht
    · obtain ⟨rfl, rfl, rfl⟩ := ht
      obtain ⟨x, rfl⟩ := hasTy_int hv'
      obtain ⟨y, rfl⟩ := hasTy_int hv2
      simp only [expectComparable, expectSameTy, if_true, sat_pure_bind, sat_pure]
      exact ⟨hF2, hX1.trans hX2, trivial, noTargets_bool⟩
    · have hty : ty = .bool := by cases op <;> inv at ht <;> exact ht.1
      subst hty
      obtain ⟨x, rfl⟩ := hasTy_bool hv'
      obtain ⟨y, rfl⟩ := hasTy_bool hv2
      simp only [expectComparable, sat_pure_bind, sat_pure]
      exact ⟨hF2, hX1.trans hX2, trivial, noTargets_bool⟩
  | conv k target a o =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨_, ta, t1, hta, t, rfl, ht⟩ := ht
    obtain ⟨ra, r1, hra, hr⟩ := hr
    have hE1 : EffLe r1.eff W.E := by
      refine EffLe.trans ?_ hE
      cases k <;> inv at hr
      all_goals first
        | (obtain ⟨s2, h2, _, rfl⟩ := hr; exact (PMono.noteAborts _ _ _ h2).2)
        | (obtain ⟨_, rfl⟩ := hr; exact EffLe.refl _)
    simp only [evalExpr]
    refine Sat.bind (ih.expr W tenv penv env s a _ _ _ _ _ _ hp hF hta hra hE1) ?_
    rintro va s1 ⟨hF1, hX1, hv, _⟩
    obtain ⟨x, rfl⟩ := hasTy_int hv
    simp only [expectInt, sat_pure_bind]
    cases target <;> inv at ht
    rename_i d
    have hty : ty = .int d := by
      cases k <;> inv at ht <;> first | exact ht.1 | exact ht.2.2.1
    subst hty
    simp only [expectIntTy, sat_pure_bind]
    split
    · exact ⟨hF1, hX1, rfl, noTargets_int⟩
    · trivial
  | _ => exact hsel.elim

/-- The elements of an array literal. -/
theorem exprs_spec (ihE : ExprSpec m prof n) {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    (hp : Perm m W) (el : Ty) (hfl : el.flat = true) :
    ∀ (es : List Expr) (s : St) (tn tn' : Nat) (rst rst' : RState),
    Frame m W tenv penv env s → tyExprsAs tenv el es tn = .ok ((), tn') →
    rpExprs penv es rst = .ok ((), rst') → EffLe rst'.eff W.E →
    Sat (mapList (evalExpr n ⟨prof, m⟩ env) es) s (fun vs s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) (Dset W) s s' ∧ vs.length = es.length ∧
      ∀ v, v ∈ vs → FlatTy el v)
  | [], s, tn, tn', rst, rst', hF, _, _, _ => by
    simp only [mapList, sat_pure]
    exact ⟨hF, Ext.refl _ _ _, rfl, fun v hv => by cases hv⟩
  | e :: rest, s, tn, tn', rst, rst', hF, ht, hr, hE => by
    simp only [tyExprsAs] at ht; inv at ht
    simp only [rpExprs] at hr; inv at hr
    obtain ⟨te, t1, hte, heq, htr⟩ := ht
    obtain ⟨re, r1, hre, hrr⟩ := hr
    have : te = el := by simpa using heq
    subst this
    simp only [mapList]
    refine Sat.bind (ihE W tenv penv env s e _ _ _ _ _ _ hp hF hte hre ((rpExprs_mono hrr).2.trans hE)) ?_
    rintro v s1 ⟨hF1, hX1, hv, _⟩
    refine Sat.bind (exprs_spec ihE hp te hfl rest s1 _ _ _ _ hF1 htr hrr hE) ?_
    rintro vs s2 ⟨hF2, hX2, hlen, hall⟩
    simp only [sat_pure]
    refine ⟨hF2, hX1.trans hX2, by simp [hlen], ?_⟩
    intro v' hv'
    rcases List.mem_cons.1 hv' with rfl | hv'
    · exact hv.flat hfl
    · exact hall v' hv'

/-- Initializers produce one independent, typed value per real field, in order. -/
theorem struct_exprs_spec (ihE : ExprSpec m prof n) {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    (hp : Perm m W) : ∀ (ts : TyList), ts.flat = true →
    ∀ (es : List Expr) (s : St) (tn tn' : Nat) (rst rst' : RState),
    Frame m W tenv penv env s → tyStructExprs tenv ts.toList es tn = .ok ((), tn') →
    rpExprs penv es rst = .ok ((), rst') → EffLe rst'.eff W.E →
    Sat (mapList (evalExpr n ⟨prof, m⟩ env) es) s (fun vs s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) (Dset W) s s' ∧ FieldsTy ts vs)
  | .nil, hf, es, s, tn, tn', rst, rst', hF, ht, hr, hE => by
    cases es with
    | nil => simp only [mapList, sat_pure]; exact ⟨hF, Ext.refl _ _ _, trivial⟩
    | cons e es => simp only [TyList.toList, tyStructExprs] at ht; inv at ht
  | .cons t ts, hf, es, s, tn, tn', rst, rst', hF, ht, hr, hE => by
    cases es with
    | nil => simp only [TyList.toList, tyStructExprs] at ht; inv at ht
    | cons e es =>
      simp only [TyList.flat, Bool.and_eq_true] at hf
      simp only [TyList.toList, tyStructExprs] at ht; inv at ht
      simp only [rpExprs] at hr; inv at hr
      obtain ⟨te, t1, hte, heq, htr⟩ := ht
      obtain ⟨re, r1, hre, hrr⟩ := hr
      have he : te = t := by simpa using heq
      subst he
      simp only [mapList]
      refine Sat.bind (ihE W tenv penv env s e _ _ _ _ _ _ hp hF hte hre
        ((rpExprs_mono hrr).2.trans hE)) ?_
      rintro v s1 ⟨hF1, hX1, hv, _⟩
      refine Sat.bind (struct_exprs_spec ihE hp ts hf.2 es s1 _ _ _ _ hF1 htr hrr hE) ?_
      rintro vs s2 ⟨hF2, hX2, hfields⟩
      simp only [sat_pure]
      exact ⟨hF2, hX1.trans hX2, hv.flat hf.1, hfields⟩

set_option maxHeartbeats 800000 in
theorem step_expr_b (ih : Specs m prof n) :
    ∀ (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (e : Expr) (tn tn' : Nat) (ty : Ty)
    (rst rst' : RState) (rho : List RootRef),
    (match e with
      | .read .. | .ref .. | .slice .. | .len .. | .push .. | .ifE .. | .blockE .. | .arrLit ..
      | .fill .. | .structLit .. => True
      | _ => False) →
    Perm m W → Frame m W tenv penv env s →
    tyExpr tenv e tn = .ok (ty, tn') → rpExpr penv e rst = .ok (rho, rst') → EffLe rst'.eff W.E →
    Sat (evalExpr (n + 1) ⟨prof, m⟩ env e) s (fun v s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) (Dset W) s s' ∧ HasTy m W.G s'.store v ty ∧
      ∀ r, Targets v r → Gam env W.P rho r) := by
  intro W tenv penv env s e tn tn' ty rst rst' rho hsel hp hF ht hr hE
  cases e with
  | read p =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨t, b, contents, t1, htp, hrd, rfl, rfl⟩ := ht
    obtain ⟨rp, r1, hrp, r2, hadd, hrr⟩ := hr
    obtain ⟨hst, hroots⟩ := readRoots_ok _ _ _ _ hrr
    simp only at hst hroots
    subst hst
    obtain ⟨_, hin⟩ := addReads_ok _ _ _ hadd
    simp only [evalExpr]
    refine Sat.bind (ih.place W tenv penv env s p _ _ _ _ _ _ _ _ hp hF htp hrp
      ((PMono.addReads _ _ _ _ hadd).2.trans hE)) ?_
    rintro l s1 ⟨hF1, hX1, hpl, hg⟩
    rcases hpl with ⟨hrt, hl⟩ | ⟨x, lv, si, v, rfl, h1, h2, rfl, rfl, hrl, h4, h5⟩ |
      ⟨x, lv, mu0, mus, E, ann, rfl, hlv, hty, rfl, hfl, hpath, hann, hgl, hlive⟩
    · have hlt := access hp hl hg (fun t' ht' => Or.inl (hE.1 t' (hin t' ht')))
      refine sat_readLoc hlt (fun v hv hT => ?_)
      exact ⟨hF1, hX1, hasTy_of_flat hT (Or.inl (readable_flat hrd hrt)), flat_no_targets hT⟩
    · refine sat_readRoot h4 ⟨hF1, hX1, h5, ?_⟩
      intro r hr'
      obtain ⟨ann, ha, hga⟩ := hF1.rooted x lv si v h1 h2 h4 r hr'
      rcases hroots with ⟨x', lv', e, _, _, ha'⟩ | ⟨x', e, _⟩ | ⟨_, hnr, _⟩
      · cases e; rw [ha] at ha'; cases ha'; exact hga
      · cases e
      · have := hnr x lv rfl (by rw [hF1.vars_p]; exact h1)
        rw [this] at hrl; cases hrl
    · -- A slice read through a reference to a slice variable of a caller.
      have hsv : penv.isRefSliceVar x = true := by
        simp [PEnv.isRefSliceVar, hF1.vars_p, hlv, hty, Ty.isRefSlice, hfl]
      rcases hroots with ⟨x', lv', e, _⟩ | ⟨x', e, _, hc⟩ | ⟨_, _, hns⟩
      · cases e
      · cases e
        obtain ⟨hnl, hann', hpr⟩ := hF1.pref x _ hc
        rw [hann] at hann'
        cases hann'
        obtain ⟨q, hq, hrq⟩ := hgl
        simp only [List.mem_singleton] at hq
        subst hq
        obtain ⟨hD, hFR, _⟩ := hpr lv mu0 mus E hlv hty _ hrq
        obtain ⟨v, hv1, hv2, hv3⟩ := hF1.sa _ E hD
        have hl : l = ⟨l.root, []⟩ := by
          cases l; simp only at hpath; simp [hpath]
        rw [hl]
        exact sat_readRoot hv1 ⟨hF1, hX1, hasTy_slice_mu hv2,
          fun r hr' => gam_of_noEnv (hFR r (hv3 r hr'))⟩
      · rw [hns x rfl] at hsv; cases hsv
  | ref mu p =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr
    obtain ⟨t, b, contents, t1, htp, hallowed, hrt, ht⟩ := ht
    have hty : ty = .ref mu t ∧ tn' = t1 := by
      rcases ht with ⟨_, _, h1, h2⟩ | ⟨_, h1, h2⟩ <;> exact ⟨h1, h2⟩
    obtain ⟨rfl, rfl⟩ := hty
    simp only [evalExpr]
    refine Sat.bind (ih.place W tenv penv env s p _ _ _ _ _ _ _ _ hp hF htp hr hE) ?_
    rintro l s1 ⟨hF1, hX1, hpl, hg⟩
    simp only [sat_pure]
    refine ⟨hF1, hX1, ?_, fun r hr' => by cases hr'; exact hg⟩
    rcases hpl with ⟨_, hl⟩ | ⟨x, lv, si, v, _, _, _, _, _, hrl, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, h3, _⟩
    · exact ⟨l, rfl, Or.inl ⟨hrt, hl⟩⟩
    · rw [refTarget_not_refLike hrt] at hrl; cases hrl
    · subst h3; simp [Ty.refTarget] at hrt
  | len v =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨el, b, t1, htv, rfl, rfl⟩ := ht
    obtain ⟨rv, r1, hrv, rfl, rfl⟩ := hr
    simp only [evalExpr]
    refine Sat.bind (ih.view W tenv penv env s v _ _ _ _ _ _ _ hp hF htv hrv hE) ?_
    rintro vw s1 ⟨hF1, hX1, _, _⟩
    simp only [sat_pure]
    exact ⟨hF1, hX1, rfl, noTargets_int⟩
  | slice mu v lo hi org =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨_, el, b, t1, htv, t2, hlo, t3, hhi, ht⟩ := ht
    have hty : ty = .slice mu el ∧ tn' = t3 := by
      rcases ht with ⟨_, _, h1, h2⟩ | ⟨_, h1, h2⟩ <;> exact ⟨h1, h2⟩
    obtain ⟨rfl, rfl⟩ := hty
    obtain ⟨rv, r1, hrv, r2, hrlo, r3, hrhi, r4, hna, rfl, rfl⟩ := hr
    have hE3 : EffLe r3.eff W.E := (PMono.noteAborts _ _ _ hna).2.trans hE
    have hE2 := (rpBound_mono hrhi).2.trans hE3
    have hE1 := (rpBound_mono hrlo).2.trans hE2
    simp only [evalExpr]
    refine Sat.bind (ih.view W tenv penv env s v _ _ _ _ _ _ _ hp hF htv hrv hE1) ?_
    rintro vw s1 ⟨hF1, hX1, hvw, hg⟩
    refine Sat.bind (ih.bound W tenv penv env s1 lo vw.len 0 _ _ _ _ hp hF1 hlo hrlo hE2) ?_
    rintro lo' s2 ⟨hF2, hX2⟩
    refine Sat.bind (ih.bound W tenv penv env s2 hi vw.len vw.len _ _ _ _ hp hF2 hhi hrhi hE3) ?_
    rintro hi' s3 ⟨hF3, hX3⟩
    by_cases hc : 0 ≤ lo' ∧ lo' ≤ hi' ∧ hi' ≤ (vw.len : Int)
    · simp only [hc, and_self, if_true, sat_pure]
      have hvw3 := (hvw.mono hX2.le).mono hX3.le
      exact ⟨hF3, (hX1.trans hX2).trans hX3,
        ⟨_, _, _, rfl, hvw3.1, hvw3.2.1.sub (by omega)⟩, fun r hr' => by cases hr'; exact hg⟩
    · simp only [hc, if_false, sat_abort]
  | push owner a =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨t, b, contents, t1, htp, ht⟩ := ht
    obtain ⟨rp, r1, hrp, ra, r2, hra, r3, hgr, rfl, rfl⟩ := hr
    obtain ⟨_, hin⟩ := addGrows_ok _ _ _ hgr
    have hE2 : EffLe r2.eff W.E := (PMono.addGrows _ _ _ _ hgr).2.trans hE
    cases t <;> inv at ht
    rename_i el
    obtain ⟨ta, t2, hta, heq, _, rfl, rfl⟩ := ht
    have : ta = el := by simpa using heq
    subst this
    simp only [evalExpr]
    refine Sat.bind (ih.place W tenv penv env s owner _ _ _ _ _ _ _ _ hp hF htp hrp
      ((rpExpr_mono hra).2.trans hE2)) ?_
    rintro l s1 ⟨hF1, hX1, hpl, hg⟩
    refine Sat.bind (ih.expr W tenv penv env s1 a _ _ _ _ _ _ hp hF1 hta hra hE2) ?_
    rintro v s2 ⟨hF2, hX2, hv, _⟩
    rcases hpl with ⟨hrt, hl⟩ | ⟨x, lv, si, v', _, _, _, _, _, hrl, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, h3, _⟩
    · have hfl : ta.flat = true := by simpa [Ty.refTarget] using hrt
      have hlt := access hp (hl.mono hX2.le) hg
        (fun t' ht' => Or.inr (Or.inr (hE.2.2.1 t' (hin t' ht'))))
      have hvs : ∀ (i : Nat) (e : Val), (#[v] : Array Val)[i]? = some e → FlatTy ta e := by
        intro i e he
        cases i <;> simp at he
        subst he; exact hv.flat hfl
      refine sat_appendLoc_bind hlt (fun st' i happ => ?_)
      simp only [sat_pure]
      have hstep := append_flatStep _ _ _ _ _ _ hlt hvs happ
      obtain ⟨_, _, es, hread, hi, hnew⟩ := append_le _ _ _ _ _ _ hlt hvs happ
      refine ⟨hF2.flatStep hstep, (hX1.trans hX2).trans (Ext.of_flatStep hstep),
        ⟨_, rfl, Or.inl ⟨flat_refTarget hfl, Or.inl ⟨v, ?_, hv.flat hfl⟩⟩⟩,
        fun r hr' => by cases hr'; exact hg⟩
      have := hnew 0 v (by simp)
      simpa using this
    · simp [Ty.isRefLike] at hrl
    · cases h3
  | ifE c t f =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨tc, t1, htc, rfl, tt, t2, htt, ft, t3, htf, heq, rfl, rfl⟩ := ht
    obtain ⟨rc, r1, hrc, rt, lt1, lt2, r2, hrt, rf, lf1, lf2, r3, hrf, rfl, rfl⟩ := hr
    have hft : ft = ty := by
      have : ty = ft := by simpa using heq
      exact this.symm
    subst hft
    simp only [evalExpr]
    refine Sat.bind (ih.expr W tenv penv env s c _ _ _ _ _ _ hp hF htc hrc
      ((rpBlockValue_mono hrt).2.trans ((rpBlockValue_mono hrf).2.trans hE))) ?_
    rintro vc s1 ⟨hF1, hX1, hv, _⟩
    obtain ⟨x, rfl⟩ := hasTy_bool hv
    simp only [expectBool, sat_pure_bind]
    cases x
    · simp only [Bool.false_eq_true, if_false]
      refine (ih.blockValue W tenv penv env s1 f _ _ _ _ _ _ _ hp hF1 htf hrf hE).mono ?_
      rintro v s2 ⟨hF2, hX2, hv2, hg⟩
      exact ⟨hF2, hX1.trans hX2, hv2, fun r hr' => (hg r hr').subset (unionRoots_right _ _)⟩
    · simp only [if_true]
      refine (ih.blockValue W tenv penv env s1 t _ _ _ _ _ _ _ hp hF1 htt hrt
        ((rpBlockValue_mono hrf).2.trans hE)).mono ?_
      rintro v s2 ⟨hF2, hX2, hv2, hg⟩
      exact ⟨hF2, hX1.trans hX2, hv2, fun r hr' => (hg r hr').subset (unionRoots_left _ _)⟩
  | blockE b =>
    simp only [tyExpr] at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨rho', l1, l2, r1, hrb, rfl, rfl⟩ := hr
    simp only [evalExpr]
    exact ih.blockValue W tenv penv env s b _ _ _ _ _ _ _ hp hF ht hrb hE
  | structLit t es =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨d, t1, hdef, hlen, t2, hes, rfl, rfl⟩ := ht
    obtain ⟨r1, hres, rfl, rfl⟩ := hr
    obtain ⟨sid, ts, rfl, hflat, hc, hd, rfl⟩ := structDef_ok _ _ _ _ _ hdef
    have htypes : ts.toList = d.fields.toList.map (·.ty) := by
      simp only [Module.structType?, hd, Option.map_some, Option.some.injEq, Ty.structT.injEq] at hc
      obtain ⟨_, rfl⟩ := hc
      exact tyList_toList_ofList _
    simp only [evalExpr]
    rw [← htypes] at hes
    refine Sat.bind (struct_exprs_spec ih.expr hp ts (by simpa [Ty.flat] using hflat)
      es s _ _ _ _ hF hes hres hE) ?_
    rintro vs s1 ⟨hF1, hX1, hfields⟩
    simp only [sat_pure]
    exact ⟨hF1, hX1, ⟨rfl, by simpa using hfields⟩, fun r h => h.elim⟩
  | arrLit t es =>
    simp only [tyExpr] at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨r1, hres, rfl, rfl⟩ := hr
    simp only [evalExpr]
    cases t <;> inv at ht
    · rename_i el k
      obtain ⟨hcanon, hfl, hlen, t1, hes, rfl, rfl⟩ := ht
      refine Sat.bind (exprs_spec ih.expr hp el hfl es s _ _ _ _ hF hes hres hE) ?_
      rintro vs s1 ⟨hF1, hX1, hl, hall⟩
      simp only [expectArrayLit, sat_pure]
      refine ⟨hF1, hX1, ⟨by simp [hl, hlen], ?_⟩, fun r hr' => hr'.elim⟩
      intro i e he
      exact hall e (by simpa using List.mem_of_getElem? (by simpa using he))
    · rename_i el
      obtain ⟨hcanon, hfl, t1, hes, rfl, rfl⟩ := ht
      refine Sat.bind (exprs_spec ih.expr hp el hfl es s _ _ _ _ hF hes hres hE) ?_
      rintro vs s1 ⟨hF1, hX1, hl, hall⟩
      simp only [expectArrayLit, sat_pure]
      refine ⟨hF1, hX1, ⟨rfl, ?_⟩, fun r hr' => hr'.elim⟩
      intro i e he
      exact hall e (by simpa using List.mem_of_getElem? (by simpa using he))
  | fill t a =>
    simp only [tyExpr] at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨ra, r1, hra, rfl, rfl⟩ := hr
    simp only [evalExpr]
    cases t <;> inv at ht
    rename_i el k
    obtain ⟨hcanon, hfl, ta, t1, hta, heq, rfl, rfl⟩ := ht
    have : ta = el := by simpa using heq
    subst this
    simp only [expectFixedCount, sat_pure_bind]
    refine Sat.bind (ih.expr W tenv penv env s a _ _ _ _ _ _ hp hF hta hra hE) ?_
    rintro v s1 ⟨hF1, hX1, hv, _⟩
    simp only [sat_pure]
    refine ⟨hF1, hX1, ⟨by simp, ?_⟩, fun r hr' => hr'.elim⟩
    intro i e he
    have : e = v := by
      rw [Array.getElem?_replicate] at he
      split at he <;> simp_all
    subst this
    exact hv.flat hfl
  | _ => exact hsel.elim

end Goose.Core.Sound

import Goose.Core.Sound.Spec

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
      Frame m W tenv penv env s' ∧ Ext (insts env) s s' ∧ HasTy m W.G s'.store v ty ∧
      ∀ r, Targets v r → Gam env W.P rho r) := by
  intro W tenv penv env s e tn tn' ty rst rst' rho hsel hp hF ht hr hE
  cases e with
  | lit t v =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨_, rfl, rfl⟩ := ht
    obtain ⟨rfl, rfl⟩ := hr
    simp only [evalExpr, sat_pure]
    exact ⟨hF, Ext.refl _ _, rfl, noTargets_int⟩
  | bool b =>
    simp only [tyExpr] at ht; inv at ht
    simp only [rpExpr] at hr; inv at hr
    obtain ⟨rfl, rfl⟩ := ht
    obtain ⟨rfl, rfl⟩ := hr
    simp only [evalExpr, sat_pure]
    exact ⟨hF, Ext.refl _ _, trivial, noTargets_bool⟩
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

end Goose.Core.Sound

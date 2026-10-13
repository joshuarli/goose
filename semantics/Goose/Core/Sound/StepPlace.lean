import Goose.Core.Sound.StepAux

/-!
One step of the induction on fuel for places, views, slice bounds and call
arguments.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {n : Nat}

theorem step_place (hm : ModOk m) (ih : Specs m prof n) : PlaceSpec m prof (n + 1) := by
  intro W tenv penv env s p tn tn' t mu contents rst rst' rho hp hF ht hr hE
  cases p with
  | var x =>
    simp only [tyPlace] at ht; inv at ht
    simp only [rpPlace] at hr; inv at hr
    obtain ⟨hx, lv0, hlv0, rfl, rfl, rfl, rfl⟩ := ht
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨lv, si, v, h1, h2, h3, h4, h5⟩ := hF.vis x hx hx
    rw [hF.vars_t, h1] at hlv0
    cases hlv0
    simp only [evalPlace, rootOf, h1, h2, sat_pure_bind, sat_pure]
    refine ⟨hF, Ext.refl _ _ _, ?_, ⟨.local x, by simp, lv0, si, h1, h2, rfl⟩⟩
    by_cases hrl : lv0.ty.isRefLike = true
    · exact Or.inr (Or.inl ⟨x, lv0, si, v, rfl, h1, h2, rfl, rfl, hrl, h4, h5⟩)
    · have hrl' : lv0.ty.isRefLike = false := by simpa using hrl
      exact Or.inl ⟨storable_refTarget h3 hrl', Or.inl (locTy_root h4 (hasTy_nonref_flat h5 h3 hrl'))⟩
  | global g =>
    simp only [tyPlace] at ht; inv at ht
    obtain ⟨_, ht⟩ := ht
    simp only [rpPlace] at hr; inv at hr
    obtain ⟨rfl, rfl⟩ := hr
    cases hg : tenv.mod.globals[g]? with
    | none => simp only [hg] at ht; inv at ht
    | some gl =>
      simp only [hg] at ht; inv at ht
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
      rw [hF.mod_t] at hg
      have hok := hm.glob g gl hg
      simp only [evalPlace, sat_pure]
      refine ⟨hF, Ext.refl _ _ _, Or.inl ⟨storable_refTarget (paramOk_of_storable hok.ty.1) hok.ty.2, ?_⟩,
        ⟨.global g, by simp, rfl⟩⟩
      by_cases hG : g < W.G
      · exact Or.inl (hF.inv.globals g gl hG hg)
      · exact Or.inr ⟨g, gl, Nat.le_of_not_lt hG, rfl, hg, FieldPath.root _⟩
  | deref e =>
    simp only [rpPlace] at hr
    simp only [evalPlace]
    cases hs : sliceRefTy tenv e with
    | none =>
      simp only [tyPlace, hs] at ht; inv at ht
      obtain ⟨te, t1, ⟨te', t0, hte, hnr, rfl, rfl⟩, ht⟩ := ht
      cases te <;> inv at ht
      rename_i mm tt
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
      refine Sat.bind (ih.expr W tenv penv env s e _ _ _ _ _ _ hp hF hte hr hE) ?_
      rintro v s1 ⟨hF1, hX1, hv, hg⟩
      obtain ⟨l, rfl, hh⟩ := hv
      simp only [expectRef, sat_pure]
      rcases hh with ⟨hrt, hl⟩ | ⟨hsl, _⟩
      · exact ⟨hF1, hX1, Or.inl ⟨hrt, hl⟩, hg _ rfl⟩
      · rw [isRefSlice_ref] at hnr; exact absurd hsl hnr
    | some ty =>
      simp only [tyPlace, hs] at ht
      obtain ⟨x, lv, mu0, mus, E, rfl, hx, hlv, hty, hfl, rfl⟩ := sliceRefTy_some hs
      rw [hty] at ht; inv at ht
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨rp, r1, hrp, r2, hadd, hrr⟩ := hr
      obtain ⟨_, hroots⟩ := readRoots_ok _ _ _ _ hrr
      refine Sat.bind (sat_read_var (prof := prof) hF hx n
        (Q := fun v s' => s' = s ∧ ∃ l, v = .ref l ∧ l.path = [] ∧
          s.store.roots[l.root]? ≠ none ∧
          ∃ ann, penv.ann x = some ann ∧ Gam env W.P ann l.root) ?_) ?_
      · intro lv' si v h1 h2 h4 h5
        rw [hF.vars_t, h1] at hlv
        cases hlv
        rw [hty] at h5
        obtain ⟨l, rfl, hh⟩ := h5
        rcases hh with ⟨hrt, _⟩ | ⟨_, hpath, hlive⟩
        · simp [Ty.refTarget] at hrt
        · exact ⟨rfl, l, rfl, hpath, hlive, hF.rooted x _ si _ h1 h2 h4 _ rfl⟩
      · rintro v s1 ⟨rfl, l, rfl, hpath, hlive, ann, hann, hgl⟩
        simp only [expectRef, sat_pure]
        rw [hF.vars_t] at hlv
        refine ⟨hF, Ext.refl _ _ _, Or.inr (Or.inr ⟨x, lv, mu0, mus, E, ann, rfl, hlv, hty, rfl, hfl, hpath,
          hann, hgl, hlive⟩), ?_⟩
        rcases hroots with ⟨x', lv', e, _, _, ha'⟩ | ⟨x', e, _⟩ | ⟨_, hnr, _⟩
        · cases e
          simp only at ha'
          rw [hann] at ha'; cases ha'; exact hgl
        · cases e
        · have := hnr x lv rfl (by rw [hF.vars_p]; exact hlv)
          rw [hty] at this; simp [Ty.isRefLike] at this
  | field owner i =>
    simp only [tyPlace] at ht; inv at ht
    obtain ⟨ot, ob, oc, t1, howner, f, t2, hfield, rfl, rfl, rfl, rfl⟩ := ht
    obtain ⟨sid, ts, rfl, hflat, hselector, rfl⟩ := structField_ok _ _ _ _ _ _ hfield
    have hf : f.ty.flat = true := tyList_flat_get ts (by simpa [Ty.flat] using hflat) i f.ty hselector
    simp only [rpPlace] at hr
    simp only [evalPlace]
    refine Sat.bind (ih.place W tenv penv env s owner _ _ _ _ _ _ _ _ hp hF howner hr hE) ?_
    rintro l s1 ⟨hF1, hX1, hpl, hg⟩
    simp only [sat_pure]
    refine ⟨hF1, hX1, ?_, hg⟩
    rcases hpl with ⟨hrt, hl⟩ | ⟨x, lv, si, v, _, _, _, _, hty, hrl, _⟩ |
      ⟨x, lv, mu0, mus, E, ann, _, _, _, hty, _⟩
    · exact Or.inl ⟨flat_refTarget hf,
        hl.fieldPath (FieldPath.field hselector (FieldPath.root _))⟩
    · simp [Ty.isRefLike] at hrl
    · cases hty
  | elem v i org =>
    simp only [tyPlace] at ht; inv at ht
    simp only [rpPlace] at hr; inv at hr
    obtain ⟨_, el, b, t1, htv, ti, t2, hti, it, rfl, rfl, rfl, rfl, rfl⟩ := ht
    obtain ⟨rv, r1, hrv, ri, r2, hri, r3, hna, rfl, rfl⟩ := hr
    have hE2 : EffLe r2.eff W.E := (PMono.noteAborts _ _ _ hna).2.trans hE
    simp only [evalPlace]
    refine Sat.bind (ih.view W tenv penv env s v _ _ _ _ _ _ _ hp hF htv hrv
      ((rpExpr_mono hri).2.trans hE2)) ?_
    rintro vw s1 ⟨hF1, hX1, hvw, hg⟩
    refine Sat.bind (ih.expr W tenv penv env s1 i _ _ _ _ _ _ hp hF1 hti hri hE2) ?_
    rintro vi s2 ⟨hF2, hX2, hvi, _⟩
    obtain ⟨k, rfl⟩ := hasTy_int hvi
    simp only [expectInt, sat_pure_bind]
    by_cases hk : 0 ≤ k ∧ k < (vw.len : Int)
    · simp only [hk, and_self, if_true, sat_pure]
      have hvw2 := hvw.mono hX2.le
      refine ⟨hF2, hX1.trans hX2, Or.inl ⟨flat_refTarget hvw2.1, Or.inl ?_⟩, hg⟩
      exact sliceTy_elem hvw2.2.1 (i := k.toNat) (by omega)
    · simp only [hk, if_false, sat_abort]

theorem step_view (ih : Specs m prof n) : ViewSpec m prof (n + 1) := by
  intro W tenv penv env s v tn tn' el mu rst rst' rho hp hF ht hr hE
  cases v with
  | of p =>
    simp only [tyView] at ht; inv at ht
    simp only [rpView] at hr; inv at hr
    obtain ⟨tp, b, contents, t1, htp, ht⟩ := ht
    obtain ⟨rp, r1, hrp, r2, hadd, rfl, rfl⟩ := hr
    obtain ⟨_, hin⟩ := addReads_ok _ _ _ hadd
    simp only [evalView]
    refine Sat.bind (ih.place W tenv penv env s p _ _ _ _ _ _ _ _ hp hF htp hrp
      ((PMono.addReads _ _ _ _ hadd).2.trans hE)) ?_
    rintro l s1 ⟨hF1, hX1, hpl, hg⟩
    have hacc : ∀ T, LocOk m W.G s1.store l T → LocTy s1.store l T := fun T hl =>
      access hp hl hg (fun t ht' => Or.inl (hE.1 t (hin t ht')))
    cases tp <;> inv at ht
    · rename_i el' k
      obtain ⟨rfl, rfl, rfl⟩ := ht
      rcases hpl with ⟨hrt, hl⟩ | ⟨x, lv, si, v, _, _, _, _, _, hrl, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, h3, _⟩
      · have hlt := hacc _ hl
        refine sat_readLoc_bind hlt (fun v hv hT => ?_)
        cases v <;> simp only [FlatTy] at hT
        rename_i es
        simp only [expectArray, sat_pure_bind, sat_pure]
        refine ⟨hF1, hX1, ⟨by simpa [Ty.refTarget] using hrt, ?_, by simp⟩, hg⟩
        rw [hT.1]; exact sliceTy_of_arr hlt
      · simp [Ty.isRefLike] at hrl
      · cases h3
    · rename_i el'
      obtain ⟨rfl, rfl, rfl⟩ := ht
      rcases hpl with ⟨hrt, hl⟩ | ⟨x, lv, si, v, _, _, _, _, _, hrl, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, h3, _⟩
      · have hlt := hacc _ hl
        refine sat_readLoc_bind hlt (fun v hv hT => ?_)
        cases v <;> simp only [FlatTy] at hT
        rename_i E' es
        simp only [expectArray, sat_pure_bind, sat_pure]
        exact ⟨hF1, hX1, ⟨by simpa [Ty.refTarget] using hrt, sliceTy_of_grow hlt hv,
          fun _ => ⟨rfl, Or.inl hlt⟩⟩, hg⟩
      · simp [Ty.isRefLike] at hrl
      · cases h3
    · rename_i el'
      obtain ⟨rfl, rfl, rfl⟩ := ht
      rcases hpl with ⟨hrt, hl⟩ | ⟨x, lv, si, v, _, _, _, _, _, hrl, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, h3, _⟩
      · have hlt := hacc _ hl
        refine sat_readLoc_bind hlt (fun v hv hT => ?_)
        cases v <;> simp only [FlatTy] at hT
        rename_i E' es
        simp only [expectArray, sat_pure_bind, sat_pure]
        exact ⟨hF1, hX1, ⟨by simpa [Ty.refTarget] using hrt, sliceTy_of_growshrink hlt hv,
          fun _ => ⟨rfl, Or.inr hlt⟩⟩, hg⟩
      · simp [Ty.isRefLike] at hrl
      · cases h3
    · rename_i el' capacity
      obtain ⟨rfl, rfl, rfl⟩ := ht
      rcases hpl with ⟨hrt, hl⟩ | ⟨x, lv, si, v, _, _, _, _, _, hrl, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, h3, _⟩
      · have hlt := hacc _ hl
        refine sat_readLoc_bind hlt (fun v hv hT => ?_)
        cases v <;> simp only [FlatTy] at hT
        rename_i E' capacity' slots len
        have hread : s1.store.read l = .ok (.limited el capacity slots len) := by
          rw [hT.1, hT.2.1]
          exact hv
        simp only [expectArray, sat_pure_bind, sat_pure]
        exact ⟨hF1, hX1, ⟨by simpa [Ty.refTarget] using hrt,
          sliceTy_of_limited hlt hread, by simp⟩, hg⟩
      · simp [Ty.isRefLike] at hrl
      · cases h3
  | val e =>
    simp only [tyView] at ht; inv at ht
    obtain ⟨te, t1, hte, ht⟩ := ht
    simp only [rpView] at hr
    simp only [evalView]
    cases te <;> inv at ht
    rename_i mm el'
    obtain ⟨rfl, rfl, rfl⟩ := ht
    refine Sat.bind (ih.expr W tenv penv env s e _ _ _ _ _ _ hp hF hte hr hE) ?_
    rintro v s1 ⟨hF1, hX1, hv, hg⟩
    obtain ⟨l, st, len, rfl, hfl, hsl⟩ := hv
    simp only [expectSlice, sat_pure_bind, sat_pure]
    exact ⟨hF1, hX1, ⟨hfl, hsl, by simp⟩, hg _ rfl⟩

theorem step_bound (ih : Specs m prof n) : BoundSpec m prof (n + 1) := by
  intro W tenv penv env s b len d tn tn' rst rst' hp hF ht hr hE
  cases b with
  | omitted =>
    simp only [evalBound, sat_pure]
    exact ⟨hF, Ext.refl _ _ _⟩
  | expr e =>
    simp only [tyBound] at ht; inv at ht
    simp only [rpBound] at hr; inv at hr
    obtain ⟨te, t1, hte, it, rfl, rfl⟩ := ht
    obtain ⟨re, hre⟩ := hr
    simp only [evalBound]
    refine Sat.bind (ih.expr W tenv penv env s e _ _ _ _ _ _ hp hF hte hre hE) ?_
    rintro v s1 ⟨hF1, hX1, hv, _⟩
    obtain ⟨k, rfl⟩ := hasTy_int hv
    simp only [expectInt, sat_pure_bind, sat_pure]
    exact ⟨hF1, hX1⟩
  | fromEnd e =>
    simp only [tyBound] at ht; inv at ht
    simp only [rpBound] at hr; inv at hr
    obtain ⟨te, t1, hte, it, rfl, rfl⟩ := ht
    obtain ⟨re, hre⟩ := hr
    simp only [evalBound]
    refine Sat.bind (ih.expr W tenv penv env s e _ _ _ _ _ _ hp hF hte hre hE) ?_
    rintro v s1 ⟨hF1, hX1, hv, _⟩
    obtain ⟨k, rfl⟩ := hasTy_int hv
    simp only [expectInt, sat_pure_bind, sat_pure]
    exact ⟨hF1, hX1⟩

theorem step_arg (ih : Specs m prof n) : ArgSpec m prof (n + 1) := by
  intro W tenv penv env s a tn tn' ty rst rst' rho hp hF ht hr hE
  cases a with
  | byVal e =>
    simp only [evalArg]
    exact ih.expr W tenv penv env s e _ _ _ _ _ _ hp hF ht hr hE
  | byRef mu p =>
    obtain ⟨t, mu', htp, hrt, rfl⟩ := ht
    simp only [evalArg]
    refine Sat.bind (ih.place W tenv penv env s p _ _ _ _ _ _ _ _ hp hF htp hr hE) ?_
    rintro l s1 ⟨hF1, hX1, hpl, hg⟩
    simp only [sat_pure]
    refine ⟨hF1, hX1, ?_, fun r hr' => by cases hr'; exact hg⟩
    rcases hpl with ⟨hrt1, hl⟩ | ⟨x, lv, si, v, _, _, _, rfl, _, hrl, h4, h5⟩ |
      ⟨x, lv, mu0, mus, E, ann, _, hlv, hty, rfl, hfl, hpath, hann, hgl, hlive⟩
    · exact ⟨l, rfl, Or.inl ⟨hrt1, hl⟩⟩
    · rcases hrt with hrt | ⟨hsl, _, _⟩
      · rw [refTarget_not_refLike hrt] at hrl; cases hrl
      · exact ⟨_, rfl, Or.inr ⟨hsl, rfl, by rw [h4]; simp⟩⟩
    · -- The pointee is a slice variable of a caller, which the store holds.
      exact ⟨l, rfl, Or.inr ⟨by simpa [Ty.isSlice] using hfl, hpath, hlive⟩⟩

end Goose.Core.Sound

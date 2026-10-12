import Goose.Core.Sound.StepCall

/-!
The steps for a call expression and for entering a callee.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {n : Nat}

set_option maxHeartbeats 1600000 in
theorem step_expr_call (hm : ModOk m) (ih : Specs m prof n) (W : World) (tenv : TEnv) (penv : PEnv)
    (env : Env) (s : St) (c : ContextId) (args : List Arg) (o : OriginId) (tn tn' : Nat) (ty : Ty)
    (rst rst' : RState) (rho : List RootRef) (hp : Perm m W) (hF : Frame m W tenv penv env s)
    (ht : tyExpr tenv (.call c args o) tn = .ok (ty, tn'))
    (hr : rpExpr penv (.call c args o) rst = .ok (rho, rst')) (hE : EffLe rst'.eff W.E) :
    Sat (evalExpr (n + 1) ⟨prof, m⟩ env (.call c args o)) s (fun v s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) s s' ∧ HasTy m W.G s'.store v ty ∧
      ∀ r, Targets v r → Gam env W.P rho r) := by
  simp only [rpExpr] at hr; inv at hr
  obtain ⟨ars, r1, hra, hrc⟩ := hr
  have hE1 := (PMono.rpCall _ _ _ _ _ _ hrc).2.trans hE
  obtain ⟨cctx, callee, hc, hi, hchk, hst, hres⟩ := rpCall_ok _ _ _ _ _ _ hrc
  rw [hF.mod_p] at hc hi
  have hc' : tenv.mod.contexts[c]? = some cctx := by rw [hF.mod_t]; exact hc
  have hi' : tenv.mod.impls[cctx.impl]? = some callee := by rw [hF.mod_t]; exact hi
  simp only [tyExpr, hc', hi'] at ht; inv at ht
  obtain ⟨_, hsize, t1, hta, t2, _, hty, _⟩ := ht
  obtain ⟨impl', himpl', hctxOk⟩ := hm.ctx c cctx hc
  rw [hi] at himpl'
  cases himpl'
  have himplOk := hm.impl _ _ hi
  simp only [evalExpr]
  refine Sat.bind (args_spec ih.arg hp callee args callee.params.toList s _ _ _ _ _ hF
    (by simpa using hsize) hta hra hE1) ?_
  rintro vals s1 ⟨hF1, hX1, hlen, hall⟩
  have hcall := ih.call W.G (fun j r => Gam env W.P (ars[j]?.getD []) r) env.depth c vals s1 cctx
    callee hc hi hF1.inv (by rw [hlen]; exact hsize.symm)
    (by
      intro i v hi_
      obtain ⟨p, pv, ar, g1, g2, g3, g4, g5⟩ := hall i v hi_
      have hp_i : callee.params[i]? = some p := by simpa using g1
      have hlt : i < callee.params.size := (Array.getElem?_eq_some_iff.1 hp_i).1
      obtain ⟨hvar, _⟩ := himplOk.params i p hp_i
      rw [hvar] at g2
      refine ⟨pv, g2, g4, fun r hr' => ?_⟩
      have href : pv.ty.isRefLike = true := by
        cases h : pv.ty.isRefLike with
        | true => rfl
        | false => exact absurd hr'.isRef (g4.not_ref h)
      obtain ⟨pv', k1, k2⟩ := checkArgRoots_ok callee cctx ars i p (hchk i hlt) hp_i
      rw [hvar, g2] at k1
      cases k1
      obtain ⟨ann, ha, hcase⟩ := k2 href
      rw [hvar] at ha
      refine ⟨ann, ha, ?_⟩
      have hgar : Gam env W.P ar r := g5 r hr'
      have hPc : Gam env W.P (ars[i]?.getD []) r := by rw [g3]; exact hgar
      rcases hcase with rfl | hsub
      · exact ⟨.param i, by simp, hPc⟩
      · obtain ⟨q, hq, hrq⟩ := hgar
        have hq' : q ∈ ann := hsub q (by rw [g3]; exact hq)
        rcases hctxOk.paramAnn i ann hlt ha q hq' with e | ⟨g, e⟩
        · subst e; exact ⟨.param i, hq', hPc⟩
        · subst e; exact ⟨.global g, hq', hrq⟩)
    (fun i a si x h => hF1.gam_older h a si x rfl)
    (by
      rcases hp with hp | ⟨hunk, hall'⟩
      · exact Or.inl hp
      · right
        have heff := callEffects_ok callee cctx ars r1.eff
        cases hs : callee.summary with
        | unknown =>
          rw [hs] at heff
          have := hE.2.2.2 (by rw [hst]; exact heff)
          rw [hunk] at this; cases this
        | known sm =>
          rw [hs] at heff
          obtain ⟨e1, e2, e3⟩ := heff
          obtain ⟨_, _, st, _, _, hcs⟩ := hctxOk.body
          obtain ⟨_, _, _, _, hpar⟩ := checkSummary_ok _ _ _ hcs sm hs
          refine ⟨sm, hs, fun t ht' => ?_⟩
          rcases ht' with ht' | ht' | ht'
          · exact expand_ok (env := env) (P := W.P) (fun j r h => h) hctxOk sm.reads
              (fun j hj => hpar j (Or.inl hj))
              (fun t' h' => hall' t' (Or.inl (hE.1 t' (by rw [hst]; exact e1 t' h')))) t ht'
          · exact expand_ok (env := env) (P := W.P) (fun j r h => h) hctxOk sm.writes
              (fun j hj => hpar j (Or.inr (Or.inl hj)))
              (fun t' h' => hall' t' (Or.inr (Or.inl (hE.2.1 t' (by rw [hst]; exact e2 t' h'))))) t ht'
          · exact expand_ok (env := env) (P := W.P) (fun j r h => h) hctxOk sm.grows
              (fun j hj => hpar j (Or.inr (Or.inr hj)))
              (fun t' h' => hall' t' (Or.inr (Or.inr (hE.2.2.1 t' (by rw [hst]; exact e3 t' h'))))) t ht')
  refine hcall.mono ?_
  rintro v s2 ⟨hInv2, hX2, hresv, hroots⟩
  refine ⟨hF1.outer hX2 hInv2, hX1.trans (hX2.weaken (fun _ h => by cases h)), ?_, ?_⟩
  · rcases hty with ⟨hnil, rfl⟩ | hone
    · rcases hresv with ⟨_, rfl⟩ | ⟨t, ht', hv⟩
      · rfl
      · rw [hnil] at ht'; cases ht'
    · rcases hresv with ⟨h0, _⟩ | ⟨t, ht', hv⟩
      · rw [hone] at h0; cases h0
      · rw [hone] at ht'; cases ht'; exact hv
  · intro r hr'
    obtain ⟨declared, hd, hgd⟩ := hroots r hr'
    rcases hresv with ⟨_, rfl⟩ | ⟨t, ht', hv⟩
    · exact hr'.elim
    · have href : t.isRefLike = true := by
        cases h : t.isRefLike with
        | true => rfl
        | false => exact absurd hr'.isRef (hv.not_ref h)
      have hrr : mapResultRoots ars [] declared = .ok rho := by
        simp only [callResultRoots, ht', hd, href, if_true] at hres
        exact hres
      obtain ⟨_, hmapped⟩ := mapResultRoots_ok ars declared [] rho hrr
      obtain ⟨q, hq, hrq⟩ := hgd
      have hmq := hmapped q hq
      cases q with
      | «local» y => exact hmq.elim
      | global g => exact ⟨.global g, hmq, hrq⟩
      | param j =>
        obtain ⟨a, ha, hsub⟩ := hmq
        have hga : Gam env W.P (ars[j]?.getD []) r := hrq
        simp only [ha, Option.getD_some] at hga
        exact hga.subset hsub

/-! ### Entering a callee -/

theorem pre_fst_range (f : Param × Val → VarId × Val) (hf : ∀ p v, f (p, v) = (p.var, v)) :
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

theorem pre_mem (f : Param × Val → VarId × Val) (hf : ∀ p v, f (p, v) = (p.var, v)) :
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

end Goose.Core.Sound

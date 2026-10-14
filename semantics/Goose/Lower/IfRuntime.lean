import Goose.Lower.TypedBlocks

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem stmt_if_none_loop_sim_at (n : Nat) (lc : Option LoopCtx)
    (c : Expr) (t : Core.Block) (org : OriginId)
    (le : LEnv) (ls : LS) (r : Unit) (ls' : LS) (pt : Pt)
    (cfg : Cfg) (env : Env) (cx : FnCtx) (fr : GIR.Frame) (state : St)
    (hlow : lowerStmt lc (.ifS c t none org) le ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hcounter : LoopCounterAt lc ls fr)
    (hcond : ∀ cv ls1, lowerExpr c le ls = (cv, ls1) → ls.pp = some pt →
      ExtT ls1 cx.fn.blocks → Rel cfg env cx fr ls →
      SimEAt cx pt fr (evalExpr n cfg env c)
        (fun value pt' fr' => Post cfg env cx ls fr ls1 fr' pt' [(cv, .val value)]) state)
    (hbody : ∀ after, evalExpr n cfg env c state = .ok (.bool true) after →
      ∀ ls2 vt ls3 pt2 fr2, lowerBlock lc [] false t le ls2 = (vt, ls3) →
      ls2.pp = some pt2 → ExtT ls3 cx.fn.blocks → Rel cfg env cx fr2 ls2 →
      LoopCounterAt lc ls2 fr2 →
      SimEAt cx pt2 fr2 (execBlock n cfg env [] t >>= prepareLoopFlow env lc)
        (BlockLoopPost cfg env cx ls2 fr2 ls3 lc t false vt) after) :
    SimEAt cx pt fr (execStmt (n + 1) cfg env (.ifS c t none org) >>= prepareLoopFlow env lc)
      (StatementLoopPost cfg env cx ls fr ls' lc) state := by
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨cv, ls1, h1, hw⟩ := hlow
  have hadv_w : ls1.Adv ls' := advB_ifS_none_core cv (advB_lowerBlock lc [] false t) _ _ _ _ hw
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv hadv_w
  rw [prepareLoopFlow_execStmt_if]
  unfold preparedLoopIf
  refine SimEAt.bind (hcond cv ls1 h1 hpp hext1 hrel) fun va afterCond pt1 fr1 hactualCond P1 => ?_
  refine SimEAt.expectBool fun β hva => ?_
  subst hva
  have hcv : fr1.vals[cv]? = some (.val (.bool β)) := P1.has (cv, _) (by simp)
  obtain ⟨blk1, hc1, hb1, hp1⟩ := LS.pp_some P1.pp
  rw [whenLive_some _ _ _ hc1] at hw
  simp only [bind_eq] at hw
  obtain ⟨⟨tb, jb⟩, lsf, hf, u2, ls2, hs1, vt, ls3, ha1, u4, ls4, ht, hs2⟩ := hw
  have e2 : ls2 = { lsf with cur := some tb } := by
    rw [setCur_run] at hs1; exact (Prod.mk.inj hs1).2.symm
  have e5 : ls' = { ls4 with cur := some jb } := by
    rw [setCur_run] at hs2; exact (Prod.mk.inj hs2).2.symm
  have hext4 : ExtT ls4 cx.fn.blocks := by rw [e5] at hext; exact hext
  have hadv1 := advB_lowerBlock lc [] false t _ _ _ _ ha1
  have hext3 : ExtT ls3 cx.fn.blocks := hext4.of_adv (adv_emitTerm ht)
  have hext2 : ExtT ls2 cx.fn.blocks := hext3.of_adv hadv1
  have hextf : ExtT lsf cx.fn.blocks := by rw [e2] at hext2; exact hext2
  obtain ⟨htb, hjb, hszf, hvf, hstf, hcf, hinst, hbtb, hbjb⟩ := fork_facts hf P1.pp hextf
  obtain ⟨Ttb, hTtb, hTtbp⟩ := hextf.params hbtb
  obtain ⟨Tjb, hTjb, hTjbp⟩ := hextf.params hbjb
  have hpp2 : ls2.pp = some (tb, 0) := by rw [e2]; exact LS.pp_cur hbtb
  have hst1 : ls1.stack = ls.stack := P1.rel.stack.trans hrel.stack.symm
  have hst2 : ls2.stack = ls.stack := by rw [e2]; show lsf.stack = _; rw [hstf, hst1]
  have hv2 : ls2.vals.size = ls1.vals.size := by rw [e2]; show lsf.vals.size = _; rw [hvf]
  have hrel2 : Rel cfg env cx fr1 ls2 := P1.rel.stack_eq (by rw [hst2, hst1])
  have hm1 := P1.mono
  have hinst' : instAt cx.fn pt1 = some (.term (.condbr cv tb [] jb [])) := hinst
  have a4 := adv_emitTerm ht
  have hjb3 : ls3.blocks[jb]? = some ⟨[], #[]⟩ := by
    refine hadv1.keep jb ⟨[], #[]⟩ ?_ ?_
    · rw [e2]; show some tb ≠ some jb; intro hh; have := Option.some.inj hh; nat_omega
    · rw [e2]; exact hbjb
  have hjb4 : ls4.blocks[jb]? = some ⟨[], #[]⟩ := by
    cases hce : ls3.cur with
    | none =>
      rw [emitTerm_none _ _ hce] at ht
      obtain ⟨-, rfl⟩ := Prod.mk.inj ht
      exact hjb3
    | some b3 =>
      rw [emitTerm_run _ _ hce] at ht
      obtain ⟨-, rfl⟩ := Prod.mk.inj ht
      have hb3 : b3 ≠ jb := by
        rcases hadv1.cur with h | h | ⟨c, hc, hc1, _⟩
        · rw [hce] at h; cases h
        · rw [hce, e2] at h
          have := Option.some.inj h
          nat_omega
        · rw [hce] at hc
          have := Option.some.inj hc
          have hl2 : ls2.blocks.size = ls1.blocks.size + 2 := by rw [e2]; exact hszf
          nat_omega
      show (ls3.blocks.modify b3 _)[jb]? = _
      rw [getElem?_modify_ne hb3]
      exact hjb3
  have hpp' : ls'.pp = some (jb, 0) := by rw [e5]; exact LS.pp_cur hjb4
  have hstl : ls'.stack = ls.stack := by
    rw [e5]; show ls4.stack = _
    rw [a4.stack, hadv1.stack, hst2]
  have hmono : ls.vals.size ≤ ls'.vals.size := by
    rw [e5]; show _ ≤ ls4.vals.size
    have := a4.vals; have := hadv1.vals; nat_omega
  cases β
  ·
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine SimEAt.goes (goes_condbr_else0 hinst' hcv hTjb hTjbp rfl) ?_
    exact SimEAt.ret (Or.inl ⟨rfl, Post.nil hpp' hmono P1.same (P1.rel.stack_eq (by rw [hstl, hst1]))⟩)
  · simp only [↓reduceIte]
    refine SimEAt.goes (goes_condbr_then0 hinst' hcv hTtb hTtbp rfl) ?_
    have hcounter1 := hcounter.afterPost (P1.sub (cells' := []) (by simp))
    have hcounter2 := hcounter1.sameValues (fr' := fr1) (ls' := ls2) rfl hv2
    refine SimEAt.bind (hbody afterCond hactualCond ls2 vt ls3 (tb, 0) fr1
      ha1 hpp2 hext3 hrel2 hcounter2) fun flow _ pt3 fr3 _ hpost => ?_
    rcases hpost with ⟨v, hf, _, P3⟩ | ⟨returned, returnOrg, hf, hsite⟩ | ⟨context, hloop, htransfer⟩
    · subst hf
      obtain ⟨hv4, hst4, hc4, hi3'⟩ := emitTerm_facts ht P3.pp hext4
      obtain ⟨Tjb', hTjb', hTjbp'⟩ : ∃ blk, cx.fn.blocks[jb]? = some blk ∧ blk.params = [] := ⟨Tjb, hTjb, hTjbp⟩
      have hi3 : instAt cx.fn pt3 = some (.term (.br jb [])) := hi3'
      have g2 := goes_br0 (fr := fr3) hi3 hTjb' hTjbp'
      refine SimEAt.goes g2 (SimEAt.ret (Or.inl ⟨rfl, Post.nil hpp' hmono ?_ ?_⟩))
      · exact P1.same.trans (P3.same.mono (by nat_omega)) P1.mono
      · exact P3.rel.stack_eq (by rw [hstl, hrel.stack, P3.rel.stack])
    · subst hf
      exact SimEAt.ret (Or.inr (Or.inl ⟨returned, returnOrg, rfl, hsite⟩))
    · have P12 : Post cfg env cx ls fr ls2 fr1 (tb, 0) [] :=
        Post.nil hpp2 (by rw [hv2]; exact P1.mono) P1.same hrel2
      rcases htransfer with ⟨rfl, hexit⟩ | ⟨rfl, hcontinue⟩
      · exact SimEAt.ret (StatementLoopPost.prefix hrel P12 hcounter
          (Or.inr (Or.inr ⟨context, hloop, Or.inl ⟨rfl, hexit⟩⟩)))
      · exact SimEAt.ret (StatementLoopPost.prefix hrel P12 hcounter
          (Or.inr (Or.inr ⟨context, hloop, Or.inr ⟨rfl, hcontinue⟩⟩)))

end Goose.Lower

import Goose.Lower.IfFlow

namespace Goose.Lower

open Goose.Core Goose.GIR

def WhileFlowSimulation (n : Nat) (c : Expr) (body : Core.Block) : Prop :=
  ∀ (le : LEnv) (ls ls' : LS) (hb : BlockId) (cfg : Cfg) (env : Env) (cx : FnCtx),
    lowerWhile hb (lowerExpr c)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump hb⟩) [] false body)
      le ls = ((), ls') → ls.pp = some (hb, 0) → ExtT ls' cx.fn.blocks →
    (∃ block, cx.fn.blocks[hb]? = some block ∧ block.params = []) →
    ∀ fr, Rel cfg env cx fr ls →
      SimG cx (hb, 0) fr (execWhile n cfg env c body >>= prepareReturn env)
        (StmtFlowPost cfg env cx ls fr ls')

theorem whileFlowSimulation_succ (n : Nat) (c : Expr) (body : Core.Block)
    (hokC : exprOk c = true) (ihb : ∀ lc, BlockFlowSimulation n lc body)
    (ih : WhileFlowSimulation n c body) : WhileFlowSimulation (n + 1) c body := by
  intro le ls ls' hb cfg env cx hlow hpp hext hheader fr hrel
  have hlow0 := hlow
  have hheader0 := hheader
  unfold lowerWhile at hlow
  obtain ⟨cv, ls1, h1, hw⟩ := bind_eq.mp hlow
  have aw : ls1.Adv ls' := advB_whenLive () (fun _ =>
    advB_loopBody cv (fun _ _ => advB_lowerBlock _ [] false body) (advB_emitTerm _))
    _ _ _ _ hw
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv aw
  rw [prepareReturn_execWhile]
  unfold preparedWhile
  refine SimG.bind ((claims n).expr c hokC le ls cv ls1 (hb, 0) cfg env cx fr
    h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.expectBool fun β hva => ?_
  subst hva
  have hcv : fr1.vals[cv]? = some (.val (.bool β)) := P1.has (cv, _) (by simp)
  obtain ⟨blk1, hc1, hb1, hp1⟩ := LS.pp_some P1.pp
  rw [whenLive_some _ _ _ hc1] at hw
  unfold loopBody at hw
  simp only [bind_eq] at hw
  obtain ⟨st, lsG, hg, ⟨tb, jb⟩, lsf, hf, u2, ls2, hs1, vt, ls3, ha1,
    u4, ls4, ht, hs2⟩ := hw
  rw [get_apply] at hg
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hg
  have e2 : ls2 = { lsf with cur := some tb } := by
    rw [setCur_run] at hs1; exact (Prod.mk.inj hs1).2.symm
  have e5 : ls' = { ls4 with cur := some jb } := by
    rw [setCur_run] at hs2; exact (Prod.mk.inj hs2).2.symm
  have hext4 : ExtT ls4 cx.fn.blocks := by rw [e5] at hext; exact hext
  have hadv1 := advB_lowerBlock (some ⟨ls1.stack.length, jb, .jump hb⟩) [] false body _ _ _ _ ha1
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
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine SimG.goes (goes_condbr_else0 hinst' hcv hTjb hTjbp rfl) ?_
    exact SimG.ret (Or.inl ⟨rfl, Post.nil hpp' hmono P1.same
      (P1.rel.stack_eq (by rw [hstl, hst1]))⟩)
  · simp only [↓reduceIte]
    refine SimG.goes (goes_condbr_then0 hinst' hcv hTtb hTtbp rfl) ?_
    refine SimG.bind (ihb (some ⟨ls1.stack.length, jb, .jump hb⟩) le ls2 vt ls3 (tb, 0) cfg env cx fr1 ha1 hpp2 hext3 hrel2)
      fun flow pt3 fr3 hpost => ?_
    rcases hpost with ⟨v, hf, _, P3⟩ | ⟨returned, returnOrg, hf, hsite⟩
    · subst hf
      obtain ⟨-, -, -, hi3'⟩ := emitTerm_facts ht P3.pp hext4
      obtain ⟨Thb, hThb, hThbp⟩ := hheader
      have hi3 : instAt cx.fn pt3 = some (.term (.br hb [])) := hi3'
      have hst3 : ls3.stack = ls.stack := P3.rel.stack.trans hrel.stack.symm
      have hrelH : Rel cfg env cx fr3 ls := P3.rel.stack_eq hst3.symm
      refine SimG.goes (goes_br0 (fr := fr3) hi3 hThb hThbp) ((ih le ls ls' hb cfg env cx hlow0 hpp hext hheader0 fr3 hrelH).mono ?_)
      intro flow pt' fr' hpost
      rcases hpost with ⟨hflow, P⟩ | hreturned
      · refine Or.inl ⟨hflow, ⟨P.pp, P.has, P.lt, P.mono, ?_, P.rel⟩⟩
        have hsame : Same ls.vals.size fr fr3 :=
          P1.same.trans (P3.same.mono (by rw [hv2]; exact hm1)) (Nat.le_refl _)
        exact hsame.trans P.same (Nat.le_refl _)
      · exact Or.inr hreturned
    · subst hf
      exact SimG.ret (Or.inr ⟨returned, returnOrg, rfl, hsite⟩)

theorem stmt_while_flow_sim (n : Nat) (lc : Option LoopCtx) (c : Expr) (body : Core.Block) (org : OriginId)
    (ih : WhileFlowSimulation n c body)
    (le : LEnv) (ls ls' : LS) (r : Unit) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : GIR.Frame) (hlow : lowerStmt lc (.while c body org) le ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls) :
    SimG cx pt fr (execStmt (n + 1) cfg env (.while c body org) >>= prepareReturn env)
      (StmtFlowPost cfg env cx ls fr ls') := by
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨⟨hb, ps⟩, ls1, hn, u1, ls2, ht, u2, lsH, hs, hw⟩ := hlow
  have hr : r = () := Subsingleton.elim _ _
  subst hr
  have aW := advB_lowerWhile hb (advB_lowerExpr c)
    (fun _ _ => advB_lowerBlock _ [] false body) _ _ _ _ hw
  have hextH : ExtT lsH cx.fn.blocks := hext.of_adv aW
  have eH : lsH = { ls2 with cur := some hb } := by
    rw [setCur_run] at hs; exact (Prod.mk.inj hs).2.symm
  have hext2 : ExtT ls2 cx.fn.blocks := by rw [eH] at hextH; exact hextH
  have hn0 := hn
  rw [newBlock0_run] at hn0
  obtain ⟨hids, e1⟩ := Prod.mk.inj hn0
  obtain ⟨hhb, -⟩ := Prod.mk.inj hids
  have hval1 : ls1.vals = ls.vals := by rw [← e1]
  have hst1 : ls1.stack = ls.stack := by rw [← e1]
  have hc1 : ls1.cur = ls.cur := by rw [← e1]
  obtain ⟨blk, hc, hb0, hp0⟩ := LS.pp_some hpp
  have hlt : pt.1 < ls.blocks.size := (Array.getElem?_eq_some_iff.mp hb0).1
  have hb1 : ls1.blocks[pt.1]? = some blk := by
    rw [← e1]
    exact (getElem?_push_lt hlt).trans hb0
  have hpp1 : ls1.pp = some pt := by
    have h := LS.pp_eq (hc1.trans hc) hb1
    rw [← hp0] at h
    exact h
  obtain ⟨hv2, hst2, -, hinst⟩ := emitTerm_facts ht hpp1 hext2
  have hnew : ls1.blocks[hb]? = some ⟨[], #[]⟩ := by
    rw [← hhb, ← e1]
    simp
  have hne : ls1.cur ≠ some hb := by
    rw [hc1, hc]
    intro h
    have he := Option.some.inj h
    rw [← hhb] at he
    exact Nat.ne_of_lt hlt he
  have hb2 : ls2.blocks[hb]? = some ⟨[], #[]⟩ := (adv_emitTerm ht).keep hb _ hne hnew
  have hppH : lsH.pp = some (hb, 0) := by rw [eH]; exact LS.pp_cur hb2
  obtain ⟨Thb, hThb, hThbp⟩ := hext2.params hb2
  have hrelH : Rel cfg env cx fr lsH := hrel.stack_eq (by
    rw [eH]; show ls2.stack = _; rw [hst2, hst1])
  have hsizeH : lsH.vals.size = ls.vals.size := by
    rw [eH]; show ls2.vals.size = _; rw [hv2, hval1]
  have hi : instAt cx.fn pt = some (.term (.br hb [])) := hinst
  simp only [execStmt]
  refine SimG.goes (goes_br0 hi hThb hThbp)
    ((ih le lsH ls' hb cfg env cx hw hppH hext
      ⟨Thb, hThb, hThbp⟩ fr hrelH).mono ?_)
  intro flow pt' fr' hpost
  rcases hpost with ⟨hflow, P⟩ | hreturned
  · refine Or.inl ⟨hflow, ⟨P.pp, P.has, P.lt, ?_, ?_, P.rel⟩⟩
    · rw [← hsizeH]; exact P.mono
    · rw [← hsizeH]; exact P.same
  · exact Or.inr hreturned

end Goose.Lower

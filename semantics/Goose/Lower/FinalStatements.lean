import Goose.Lower.TypedStatements

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem stmt_assert_expr_sim {n : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {results : List Ty} {loop : Option LoopCtx} {expr : Expr} {org : OriginId}
    {ls ls' : LS} {pt : Pt} {fr : GIR.Frame} {state : St}
    (source : ExprSource cfg env expr state)
    (hmetadata : SourceResults source.typingEnv source.rootsEnv results)
    (hexpr : TypedExprClaim n cfg results expr)
    (hlow : lowerStmt loop (.assertS expr org) (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hgir : cx.cfg.mod = lower cfg.mod) (hresults : cx.fn.results = results) :
    SimEAt cx pt fr (execStmt (n + 1) cfg env (.assertS expr org))
      (fun flow pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) state := by
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨cv, ls1, h1, hw⟩ := hlow
  have hadv_w : ls1.Adv ls' := advB_assert_core cv org _ _ _ _ hw
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv hadv_w
  simp only [execStmt]
  refine SimEAt.bind (hexpr env state source hmetadata ls ls1 cv pt cx fr h1 hpp hext1 hrel hgir hresults) fun va after pt1 fr1 _ P1 => ?_
  refine SimEAt.expectBool fun β hva => ?_
  subst hva
  have hcv : fr1.vals[cv]? = some (.val (.bool β)) := P1.has (cv, _) (by simp)
  obtain ⟨blk1, hc1, hb1, hp1⟩ := LS.pp_some P1.pp
  rw [whenLive_some _ _ _ hc1] at hw
  simp only [bind_eq] at hw
  obtain ⟨⟨pb, fb⟩, lsf, hf, u2, ls2, hs1, u3, ls4, ht, hs2⟩ := hw
  have e2 : ls2 = { lsf with cur := some fb } := by
    rw [setCur_run] at hs1; exact (Prod.mk.inj hs1).2.symm
  have e5 : ls' = { ls4 with cur := some pb } := by
    rw [setCur_run] at hs2; exact (Prod.mk.inj hs2).2.symm
  have hext4 : ExtT ls4 cx.fn.blocks := by rw [e5] at hext; exact hext
  have hext2 : ExtT ls2 cx.fn.blocks := hext4.of_adv (adv_emitTerm ht)
  have hextf : ExtT lsf cx.fn.blocks := by rw [e2] at hext2; exact hext2
  obtain ⟨htb, heb, hszf, hvf, hstf, hcf, hinst, hbpb, hbfb⟩ := fork_facts hf P1.pp hextf
  have hTpb := hextf.params hbpb
  have hTfb := hextf.params hbfb
  have hpp2 : ls2.pp = some (fb, 0) := by rw [e2]; exact LS.pp_cur hbfb
  obtain ⟨hv4, hst4, hc4, hiabort⟩ := emitTerm_facts ht hpp2 hext4
  have hpb4 : ls4.blocks[pb]? = some ⟨[], #[]⟩ := by
    rw [emitTerm_run _ _ (show ls2.cur = some fb by rw [e2])] at ht
    obtain ⟨-, rfl⟩ := Prod.mk.inj ht
    show (ls2.blocks.modify fb _)[pb]? = _
    rw [getElem?_modify_ne (by nat_omega)]
    rw [e2]; exact hbpb
  have hpp' : ls'.pp = some (pb, 0) := by rw [e5]; exact LS.pp_cur hpb4
  have hst1 : ls1.stack = ls.stack := P1.rel.stack.trans hrel.stack.symm
  have hstl : ls'.stack = ls.stack := by
    rw [e5]; show ls4.stack = _
    rw [hst4]; show ls2.stack = _
    rw [e2]; show lsf.stack = _
    rw [hstf, hst1]
  have hm1 := P1.mono
  have hvl : ls'.vals.size = ls1.vals.size := by
    rw [e5]; show ls4.vals.size = _
    rw [hv4]; show ls2.vals.size = _
    rw [e2]; show lsf.vals.size = _
    rw [hvf]
  have hinst' : instAt cx.fn pt1 = some (.term (.condbr cv pb [] fb [])) := hinst
  cases β
  ·
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨Tfb, hTfb', hTfbp⟩ := hTfb
    refine SimEAt.goes (goes_condbr_else0 hinst' hcv hTfb' hTfbp rfl) ?_
    exact (SimE.abort_term hiabort).at_state after
  · simp only [↓reduceIte]
    obtain ⟨Tpb, hTpb', hTpbp⟩ := hTpb
    refine SimEAt.goes (goes_condbr_then0 hinst' hcv hTpb' hTpbp rfl) ?_
    refine SimEAt.ret ⟨rfl, Post.nil hpp' (by nat_omega) ?_ ?_⟩
    · exact P1.same.mono (by nat_omega)
    · exact P1.rel.stack_eq (by rw [hstl, hst1])

theorem stmt_exit_expr_sim {n : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {results : List Ty} {loop : Option LoopCtx} {expr : Expr} {org : OriginId}
    {ls ls' : LS} {pt : Pt} {fr : GIR.Frame} {state : St}
    (source : ExprSource cfg env expr state)
    (hmetadata : SourceResults source.typingEnv source.rootsEnv results)
    (hexpr : TypedExprClaim n cfg results expr)
    (hlow : lowerStmt loop (.exit expr org) (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hgir : cx.cfg.mod = lower cfg.mod) (hresults : cx.fn.results = results) :
    SimEAt cx pt fr (execStmt (n + 1) cfg env (.exit expr org))
      (fun flow pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) state := by
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨id, middle, evaluated, terminated⟩ := hlow
  have hextMiddle := hext.of_adv (adv_emitTerm terminated)
  simp only [execStmt]
  refine SimEAt.bind (hexpr env state source hmetadata ls middle id pt cx fr evaluated hpp
    hextMiddle hrel hgir hresults) fun value after pt' fr' _ P => ?_
  refine SimEAt.expectInt fun ty number hvalue => ?_
  subst value
  have cell := P.has (id, .val (.int ty number)) (by simp)
  obtain ⟨_, _, _, instruction⟩ := emitTerm_facts terminated P.pp hext
  exact (SimE.exit_term instruction cell).at_state after

theorem typedStatementLoopSimulation_assert {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {expr : Expr} {org : OriginId}
    (hexpr : TypedExprClaim n cfg results expr) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.assertS expr org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter
  obtain ⟨child, htyping, hroots, _⟩ := source.assertChild
  have metadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  have resultEq : result = () := Subsingleton.elim _ _
  subst result
  exact (stmt_assert_expr_sim child metadata hexpr hlow hpp hext hrel hgir hresults).prepareNormalLoopFlow

theorem typedStatementLoopSimulation_exit {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {expr : Expr} {org : OriginId}
    (hexpr : TypedExprClaim n cfg results expr) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.exit expr org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter
  obtain ⟨child, _, htyping, hroots, _⟩ := source.exitChild
  have metadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    exact hmetadata
  have resultEq : result = () := Subsingleton.elim _ _
  subst result
  exact (stmt_exit_expr_sim child metadata hexpr hlow hpp hext hrel hgir hresults).prepareNormalLoopFlow

end Goose.Lower

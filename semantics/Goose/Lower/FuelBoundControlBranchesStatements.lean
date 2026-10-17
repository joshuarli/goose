import Goose.Lower.FuelBoundControlSteps
import Goose.Lower.FuelBoundTyped

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem typedStatementFuelBound_if_some {n fuel : Nat} {cfg : Cfg} {results : List Ty}
    {lc : Option LoopCtx} {c : Expr} {t fb : Core.Block} {org : OriginId}
    (conditionClaim : TypedExprFuelBound n fuel cfg results c)
    (thenClaim : ∀ residual, residual ≤ fuel → TypedBlockFuelBound n residual cfg results lc [] [] false t)
    (elseClaim : ∀ residual, residual ≤ fuel → TypedBlockFuelBound n residual cfg results lc [] [] false fb) :
    TypedStatementFuelBound (n + 1) fuel cfg results lc (.ifS c t (some fb) org) := by
  intro env state source metadata loops ls ls' pt cx fr hlow hpp hext hrel hgir hresults depth targets
    counter generated frames
  obtain ⟨condition,typing,roots,type⟩ := source.ifConditionChild
  have conditionMetadata : SourceResults condition.typingEnv condition.rootsEnv results := by
    rw [typing,roots]; exact metadata
  let le := lowerEnv cfg.mod env.vars results
  simp only [lowerStmt,bind_eq] at hlow
  obtain ⟨cv,ls1,h1,hw⟩ := hlow
  have hadv_w := advB_ifS_some_core cv (advB_lowerBlock lc [] false t)
    (advB_lowerBlock lc [] false fb) _ _ _ _ hw
  have hext1 := hext.of_adv hadv_w
  have first := conditionClaim env state condition conditionMetadata ls ls1 cv pt cx fr h1 hpp hext1
    hrel hgir hresults generated
  have composition : FuelBoundAt n fuel cx pt fr
      (fun n => preparedLoopIf n cfg env lc c t (some fb))
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr ls' lc flow pt' fr') state := by
    unfold preparedLoopIf
    simp only [bind_assoc]
    refine first.bind ?_
    · intro va afterCond pt1 fr1 hactualCond P1 branchFuel branchBound
      have typed := (condition.result n va hactualCond).typed
      rw [type] at typed
      obtain ⟨β,rfl⟩ := Core.Sound.hasTy_bool typed
      simp only [expectBool,pure_bind]
      have hcv : fr1.vals[cv]? = some (.val (.bool β)) := P1.has (cv, _) (by simp)
      obtain ⟨blk1, hc1, hb1, hp1⟩ := LS.pp_some P1.pp
      rw [whenLive_some _ _ _ hc1] at hw
      simp only [bind_eq] at hw
      obtain ⟨⟨tb, eb⟩, lsf, hf, u2, ls2, hs1, vt, ls3, ha1, endT, ls4, hc4, u5, ls5, hs2, vf, ls6, ha2,
        endF, ls7, hc7, hj⟩ := hw
      cases u2
      cases u5
      obtain ⟨e4c, e4⟩ := curBlock_eq hc4
      subst e4
      obtain ⟨e7c, e7⟩ := curBlock_eq hc7
      subst e7
      have hext6 : ExtT ls7 cx.fn.blocks := hext.of_ext (joinArms_ext hj)
      have hadv1 := advB_lowerBlock lc [] false t _ _ _ _ ha1
      have hadv2 := advB_lowerBlock lc [] false fb _ _ _ _ ha2
      obtain ⟨htb, heb, hinst, ⟨Ttb, hTtb, hTtbp⟩, ⟨Teb, hTeb, hTebp⟩, hpp2, hpp5, hst2, hv2, hst3, hst6,
        hv16, hv36, hendT, hendF, hkeep, hsz36, hsz6⟩ :=
        branch_facts hf hs1 hadv1 hs2 hadv2 P1.pp hext6
      have hpp2' : ls2.pp = some (tb, 0) := hpp2
      have hrel2 : Rel cfg env cx fr1 ls2 := P1.rel.stack_eq hst2
      have hltT : ∀ b, endT = some b → b < ls7.blocks.size := by
        intro b hb
        exact Nat.lt_of_lt_of_le (hendT b (by rw [e4c] at hb; exact hb)).1 hsz36
      have hltF : ∀ b, endF = some b → b < ls7.blocks.size := by
        intro b hb
        exact (hendF b (by rw [e7c] at hb; exact hb)).1
      have hnd : ∀ bT bF, endT = some bT → endF = some bF → bT ≠ bF := by
        intro bT bF hT hF
        obtain ⟨hlt, hne, hcase⟩ := hendT bT (by rw [e4c] at hT; exact hT)
        obtain ⟨-, hcase'⟩ := hendF bF (by rw [e7c] at hF; exact hF)
        intro hh
        subst hh
        rcases hcase' with h | h
        · exact hne h
        · nat_omega
      have hinst' : instAt cx.fn pt1 = some (.term (.condbr cv tb [] eb [])) := hinst
      have hmono_all : ls1.vals.size ≤ ls4.vals.size := by
        have := hadv1.vals; nat_omega
      have e5 : ls5 = { ls4 with cur := some eb } := by
        rw [setCur_run] at hs2; exact (Prod.mk.inj hs2).2.symm
      have hext4 : ExtT ls4 cx.fn.blocks := by
        have := hext6.of_adv hadv2
        rw [e5] at this; exact this
      have hm1 := P1.mono
      have hst1 : ls1.stack = ls.stack := P1.rel.stack.trans hrel.stack.symm
      have hst_out : ls7.stack = ls.stack := hst6.trans hst1
      have frames1 := frames.mono (advB_lowerExpr c _ _ _ _ h1).ext
      have framesF := frames1.mono (advB_fork cv _ _ _ _ hf).ext
      have e2 : ls2 = { lsf with cur := some tb } := by
        rw [setCur_run] at hs1; exact (Prod.mk.inj hs1).2.symm
      have frames2 : LoopBuilderFrames lc ls2 := framesF.of_blocks (by rw [e2])
      have frames4 := frames2.mono hadv1.ext
      have frames5 : LoopBuilderFrames lc ls5 := frames4.of_blocks (by rw [e5])
      have genF := (generated.lowerExpr c h1).fork cv hf
      have forkSize := (fork_ids hf).2
      have gen2 := genF.setCur (some tb)
        (by intro current equal; have same := Option.some.inj equal; rw [← same,htb,forkSize]; nat_omega) hs1
      have gen4 := gen2.lowerBlock lc [] false t frames2.toTargets ha1
      have gen5 := gen4.setCur (some eb)
        (by intro current equal; have same := Option.some.inj equal; rw [← same,heb]
            have bound := hadv1.ext.1
            rw [e2] at bound
            nat_omega) hs2
      cases branchFuel with
      | zero => exact FuelBoundAt.zero n _ _ _ _ _ _
      | succ branchFuel =>
        cases β
        · simp only [Bool.false_eq_true,↓reduceIte]
          have hrel5 : Rel cfg env cx fr1 ls5 := P1.rel.stack_eq (by rw [e5]; exact hst3)
          have P15 : Post cfg env cx ls fr ls5 fr1 (eb,0) [] :=
            Post.nil hpp5 (by rw [e5]; exact Nat.le_trans P1.mono hmono_all) P1.same hrel5
          obtain ⟨body,bodyTyping,bodyRoots,_,_⟩ := source.ifElseChild n hactualCond
          have bodyMetadata : SourceResults body.typingEnv body.rootsEnv results := by
            rw [bodyTyping,bodyRoots]; exact metadata
          have bodyLoops : LoopSourceMatches body.typingEnv lc := by rw [bodyTyping]; exact loops
          have reflected := elseClaim branchFuel (by omega) env afterCond body bodyMetadata bodyLoops
            ls5 ls7 vf (eb,0) cx fr1 ha2 hpp5 hext6 hrel5 trivial hgir hresults depth targets
            (counter.afterPost P15) gen5 frames5
          apply FuelBoundAt.condbr_take0 hinst' hcv hTeb hTebp rfl
          simp only [← bind_assoc]
          refine reflected.bind ?_
          intro flow after pt7 fr7 done hpost joinFuel joinBound
          rcases hpost with ⟨v,rfl,_,P7⟩ | ⟨returned,returnOrg,rfl,hsite⟩ | ⟨context,hloop,htransfer⟩
          · obtain ⟨blk7,hc7',hb7,hp7⟩ := LS.pp_some P7.pp
            have hendF' : endF = some pt7.1 := by rw [e7c]; exact hc7'
            have hlive : endT.isSome ∨ endF.isSome := Or.inr (by rw [hendF']; rfl)
            obtain ⟨hvj,hstj,hbj,hcj,hTj⟩ := joinArms_facts hj hext hlive hnd hltT hltF
            have hinstF := hTj pt7.1 blk7 (Or.inr hendF') hb7
            obtain ⟨Tjb,hTjb,hTjbp⟩ := hext.params hbj
            have hpt7 : pt7 = (pt7.1,blk7.insts.size) := Prod.ext rfl hp7
            have hi7 : instAt cx.fn pt7 = some (.term (.br ls7.blocks.size [])) := by
              rw [hpt7]; exact hinstF
            cases joinFuel with
            | zero => exact FuelBoundAt.zero n _ _ _ _ _ _
            | succ joinFuel =>
              apply FuelBoundAt.br0 hi7 hTjb hTjbp
              refine FuelBoundAt.ret (Or.inl ⟨rfl,Post.nil (LS.pp_eq hcj hbj) (by nat_omega) ?_ ?_⟩)
              · refine P1.same.trans (P7.same.mono ?_) P1.mono
                rw [e5]; exact hmono_all
              · exact P7.rel.stack_eq hstj
          · exact FuelBoundAt.ret (Or.inr (Or.inl ⟨returned,returnOrg,rfl,hsite⟩))
          · rcases htransfer with ⟨rfl,hexit⟩ | ⟨rfl,hcontinue⟩
            · exact FuelBoundAt.ret (StatementLoopPost.prefix hrel P15 counter
                (Or.inr (Or.inr ⟨context,hloop,Or.inl ⟨rfl,hexit⟩⟩)))
            · exact FuelBoundAt.ret (StatementLoopPost.prefix hrel P15 counter
                (Or.inr (Or.inr ⟨context,hloop,Or.inr ⟨rfl,hcontinue⟩⟩)))
        · simp only [↓reduceIte]
          have P12 : Post cfg env cx ls fr ls2 fr1 (tb,0) [] :=
            Post.nil hpp2' (by rw [hv2]; exact P1.mono) P1.same hrel2
          obtain ⟨body,bodyTyping,bodyRoots,_,_⟩ := source.ifThenChild n hactualCond
          have bodyMetadata : SourceResults body.typingEnv body.rootsEnv results := by
            rw [bodyTyping,bodyRoots]; exact metadata
          have bodyLoops : LoopSourceMatches body.typingEnv lc := by rw [bodyTyping]; exact loops
          have reflected := thenClaim branchFuel (by omega) env afterCond body bodyMetadata bodyLoops
            ls2 ls4 vt (tb,0) cx fr1 ha1 hpp2' hext4 hrel2 trivial hgir hresults depth targets
            (counter.afterPost P12) gen2 frames2
          apply FuelBoundAt.condbr_take0 hinst' hcv hTtb hTtbp rfl
          simp only [← bind_assoc]
          refine reflected.bind ?_
          intro flow after pt3 fr3 done hpost joinFuel joinBound
          rcases hpost with ⟨v,rfl,_,P3⟩ | ⟨returned,returnOrg,rfl,hsite⟩ | ⟨context,hloop,htransfer⟩
          · obtain ⟨blk3,hc3,hb3,hp3⟩ := LS.pp_some P3.pp
            have hendT' : endT = some pt3.1 := by rw [e4c]; exact hc3
            have hlive : endT.isSome ∨ endF.isSome := Or.inl (by rw [hendT']; rfl)
            obtain ⟨hvj,hstj,hbj,hcj,hTj⟩ := joinArms_facts hj hext hlive hnd hltT hltF
            have hne : pt3.1 ≠ eb := (hendT pt3.1 hc3).2.1
            have hb7 := hkeep pt3.1 blk3 hb3 hne
            have hinstT := hTj pt3.1 blk3 (Or.inl hendT') hb7
            obtain ⟨Tjb,hTjb,hTjbp⟩ := hext.params hbj
            have hpt3 : pt3 = (pt3.1,blk3.insts.size) := Prod.ext rfl hp3
            have hi3 : instAt cx.fn pt3 = some (.term (.br ls7.blocks.size [])) := by
              rw [hpt3]; exact hinstT
            cases joinFuel with
            | zero => exact FuelBoundAt.zero n _ _ _ _ _ _
            | succ joinFuel =>
              apply FuelBoundAt.br0 hi3 hTjb hTjbp
              refine FuelBoundAt.ret (Or.inl ⟨rfl,Post.nil (LS.pp_eq hcj hbj) (by nat_omega) ?_ ?_⟩)
              · exact P1.same.trans (P3.same.mono (by nat_omega)) P1.mono
              · exact P3.rel.stack_eq (hstj.trans (hst6.trans hst3.symm))
          · exact FuelBoundAt.ret (Or.inr (Or.inl ⟨returned,returnOrg,rfl,hsite⟩))
          · rcases htransfer with ⟨rfl,hexit⟩ | ⟨rfl,hcontinue⟩
            · exact FuelBoundAt.ret (StatementLoopPost.prefix hrel P12 counter
                (Or.inr (Or.inr ⟨context,hloop,Or.inl ⟨rfl,hexit⟩⟩)))
            · exact FuelBoundAt.ret (StatementLoopPost.prefix hrel P12 counter
                (Or.inr (Or.inr ⟨context,hloop,Or.inr ⟨rfl,hcontinue⟩⟩)))
  exact composition.of_source (otherFuel := n + 1)
    (congrFun (prepareLoopFlow_execStmt_if n cfg env lc c t (some fb) org) state)

theorem typedStatementFuelBound_if_none {n fuel : Nat} {cfg : Cfg} {results : List Ty}
    {lc : Option LoopCtx} {c : Expr} {t : Core.Block} {org : OriginId}
    (conditionClaim : TypedExprFuelBound n fuel cfg results c)
    (thenClaim : ∀ residual, residual ≤ fuel → TypedBlockFuelBound n residual cfg results lc [] [] false t) :
    TypedStatementFuelBound (n + 1) fuel cfg results lc (.ifS c t none org) := by
  intro env state source metadata loops ls ls' pt cx fr hlow hpp hext hrel hgir hresults depth targets
    hcounter generated frames
  obtain ⟨condition,typing,roots,type⟩ := source.ifConditionChild
  have conditionMetadata : SourceResults condition.typingEnv condition.rootsEnv results := by
    rw [typing,roots]; exact metadata
  let le := lowerEnv cfg.mod env.vars results
  simp only [lowerStmt,bind_eq] at hlow
  obtain ⟨cv,ls1,h1,hw⟩ := hlow
  have hadv_w := advB_ifS_none_core cv (advB_lowerBlock lc [] false t) _ _ _ _ hw
  have hext1 := hext.of_adv hadv_w
  have first := conditionClaim env state condition conditionMetadata ls ls1 cv pt cx fr h1 hpp hext1
    hrel hgir hresults generated
  have composition : FuelBoundAt n fuel cx pt fr (fun n => preparedLoopIf n cfg env lc c t none)
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr ls' lc flow pt' fr') state := by
    unfold preparedLoopIf
    simp only [bind_assoc]
    refine first.bind ?_
    · intro va afterCond pt1 fr1 hactualCond P1 branchFuel branchBound
      have typed := (condition.result n va hactualCond).typed
      rw [type] at typed
      obtain ⟨β,rfl⟩ := Core.Sound.hasTy_bool typed
      simp only [expectBool,pure_bind]
      have hcv : fr1.vals[cv]? = some (.val (.bool β)) := P1.has (cv, _) (by simp)
      obtain ⟨blk1, hc1, hb1, hp1⟩ := LS.pp_some P1.pp
      rw [whenLive_some _ _ _ hc1] at hw
      simp only [bind_eq] at hw
      obtain ⟨⟨tb, jb⟩, lsf, hf, u2, ls2, hs1, vt, ls3, ha1, u4, ls4, ht, hs2⟩ := hw
      cases u2
      cases u4
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
      have frames1 := frames.mono (advB_lowerExpr c _ _ _ _ h1).ext
      have framesF := frames1.mono (advB_fork cv _ _ _ _ hf).ext
      have frames2 : LoopBuilderFrames lc ls2 := framesF.of_blocks (by rw [e2])
      have genF := (generated.lowerExpr c h1).fork cv hf
      have gen2 := genF.setCur (some tb)
        (by intro current equal; have same := Option.some.inj equal; rw [← same,htb,hszf]; nat_omega) hs1
      cases branchFuel with
      | zero => exact FuelBoundAt.zero n _ _ _ _ _ _
      | succ branchFuel =>
        cases β
        · simp only [Bool.false_eq_true,↓reduceIte,unitFlow]
          apply FuelBoundAt.condbr_take0 hinst' hcv hTjb hTjbp rfl
          exact FuelBoundAt.ret (Or.inl ⟨rfl,
            Post.nil hpp' hmono P1.same (P1.rel.stack_eq (by rw [hstl,hst1]))⟩)
        · simp only [↓reduceIte]
          have hcounter1 := hcounter.afterPost (P1.sub (cells' := []) (by simp))
          have hcounter2 := hcounter1.sameValues (fr' := fr1) (ls' := ls2) rfl hv2
          obtain ⟨body,bodyTyping,bodyRoots,_,_⟩ := source.ifThenChild n hactualCond
          have bodyMetadata : SourceResults body.typingEnv body.rootsEnv results := by
            rw [bodyTyping,bodyRoots]; exact metadata
          have bodyLoops : LoopSourceMatches body.typingEnv lc := by rw [bodyTyping]; exact loops
          have reflected := thenClaim branchFuel (by omega) env afterCond body bodyMetadata bodyLoops
            ls2 ls3 vt (tb,0) cx fr1 ha1 hpp2 hext3 hrel2 trivial hgir hresults depth targets hcounter2 gen2 frames2
          apply FuelBoundAt.condbr_take0 hinst' hcv hTtb hTtbp rfl
          simp only [← bind_assoc]
          refine reflected.bind ?_
          intro flow after pt3 fr3 done hpost joinFuel joinBound
          rcases hpost with ⟨v,rfl,_,P3⟩ | ⟨returned,returnOrg,rfl,hsite⟩ | ⟨context,hloop,htransfer⟩
          · obtain ⟨hv4,hst4,hc4,hi3'⟩ := emitTerm_facts ht P3.pp hext4
            have hi3 : instAt cx.fn pt3 = some (.term (.br jb [])) := hi3'
            cases joinFuel with
            | zero => exact FuelBoundAt.zero n _ _ _ _ _ _
            | succ joinFuel =>
              apply FuelBoundAt.br0 hi3 hTjb hTjbp
              refine FuelBoundAt.ret (Or.inl ⟨rfl,Post.nil hpp' hmono ?_ ?_⟩)
              · exact P1.same.trans (P3.same.mono (by nat_omega)) P1.mono
              · exact P3.rel.stack_eq (by rw [hstl,hrel.stack,P3.rel.stack])
          · exact FuelBoundAt.ret (Or.inr (Or.inl ⟨returned,returnOrg,rfl,hsite⟩))
          · have P12 : Post cfg env cx ls fr ls2 fr1 (tb,0) [] :=
              Post.nil hpp2 (by rw [hv2]; exact P1.mono) P1.same hrel2
            rcases htransfer with ⟨rfl,hexit⟩ | ⟨rfl,hcontinue⟩
            · exact FuelBoundAt.ret (StatementLoopPost.prefix hrel P12 hcounter
                (Or.inr (Or.inr ⟨context,hloop,Or.inl ⟨rfl,hexit⟩⟩)))
            · exact FuelBoundAt.ret (StatementLoopPost.prefix hrel P12 hcounter
                (Or.inr (Or.inr ⟨context,hloop,Or.inr ⟨rfl,hcontinue⟩⟩)))
  exact composition.of_source (otherFuel := n + 1)
    (congrFun (prepareLoopFlow_execStmt_if n cfg env lc c t none org) state)

theorem typedStatementFuelBound_ifS {n fuel : Nat} {cfg : Cfg} {results : List Ty}
    {lc : Option LoopCtx} {c : Expr} {t : Core.Block} {otherwise : Option Core.Block} {org : OriginId}
    (condition : TypedExprFuelBound n fuel cfg results c)
    (yes : ∀ residual, residual ≤ fuel → TypedBlockFuelBound n residual cfg results lc [] [] false t)
    (no : ∀ block, otherwise = some block → ∀ residual, residual ≤ fuel →
      TypedBlockFuelBound n residual cfg results lc [] [] false block) :
    TypedStatementFuelBound (n + 1) fuel cfg results lc (.ifS c t otherwise org) := by
  cases otherwise with
  | none => exact typedStatementFuelBound_if_none condition yes
  | some block => exact typedStatementFuelBound_if_some condition yes (no block rfl)

#print axioms typedStatementFuelBound_ifS

end Goose.Lower

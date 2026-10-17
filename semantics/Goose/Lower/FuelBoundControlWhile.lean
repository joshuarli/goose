import Goose.Lower.FuelBoundTyped
import Goose.Lower.FuelBoundControlSteps
import Goose.Lower.TypedWhile

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem typedWhileFuelBound_step {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {c : Expr} {body : Core.Block} {origin : OriginId}
    (condition : TypedExprFuelBound sourceFuel fuel cfg results c)
    (blocks : ∀ residual, residual < fuel → ∀ context,
      TypedBlockFuelBound sourceFuel residual cfg results (some context) [] [] false body)
    (reentry : ∀ residual, residual < fuel → TypedWhileFuelBound sourceFuel residual cfg results c body origin) :
    TypedWhileFuelBound (sourceFuel + 1) fuel cfg results c body origin := by
  intro env state source metadata ls ls' hb cx fr hlow hpp hext hheader hrel moduleEq resultsEq generated
  have hlow0 := hlow
  obtain ⟨conditionSource,conditionTyping,conditionRoots,conditionType⟩ := source.whileConditionChild
  have conditionMetadata : SourceResults conditionSource.typingEnv conditionSource.rootsEnv results := by
    rw [conditionTyping,conditionRoots]
    exact metadata
  unfold lowerWhile at hlow
  obtain ⟨cv,ls1,h1,hw⟩ := bind_eq.mp hlow
  have aw : ls1.Adv ls' := advB_whenLive () (fun _ =>
    advB_loopBody cv (fun _ _ => advB_lowerBlock _ [] false body) (advB_emitTerm _)) _ _ _ _ hw
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv aw
  have first := condition env state conditionSource conditionMetadata ls ls1 cv (hb,0) cx fr h1 hpp
    hext1 hrel moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx (hb,0) fr
      (fun n => preparedWhile n cfg env c body)
      (fun flow _ pt' fr' => StmtFlowPost cfg env cx ls fr ls' flow pt' fr') state := by
    refine first.bind ?_
    · intro value afterCond pt1 fr1 hactualCond P1 residual bound
      have typed := (conditionSource.result sourceFuel value hactualCond).typed
      rw [conditionType] at typed
      obtain ⟨β,rfl⟩ := Core.Sound.hasTy_bool typed
      simp only [Core.expectBool,pure_bind]
      have hcv : fr1.vals[cv]? = some (.val (.bool β)) := P1.has (cv,_) (by simp)
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
      obtain ⟨localHeader, _, localHeaderAt, _⟩ := LS.pp_some hpp
      obtain ⟨finalHeader, finalHeaderAt, finalHeaderParams⟩ := (hext1.of_adv (advB_lowerExpr c _ _ _ _ h1)).params localHeaderAt
      have headerCopy := hheader
      obtain ⟨expectedHeader, expectedHeaderAt, expectedHeaderParams⟩ := headerCopy
      have sameHeader : finalHeader = expectedHeader :=
        Option.some.inj (finalHeaderAt.symm.trans expectedHeaderAt)
      have localHeaderParams : localHeader.params = [] := by
        rw [← finalHeaderParams, sameHeader]
        exact expectedHeaderParams
      have headerFrames : LoopBuilderFrames (some ⟨ls1.stack.length, hb, .jump hb⟩) ls :=
        ⟨⟨localHeader, localHeaderAt, localHeaderParams⟩, ⟨localHeader, localHeaderAt, localHeaderParams⟩⟩
      have carried := ((headerFrames.mono (advB_lowerExpr c _ _ _ _ h1).ext).mono
        (advB_fork cv _ _ _ _ hf).ext).of_blocks (setCur_blocks hs1)
      have bodyFrames : LoopBuilderFrames (some ⟨ls1.stack.length, jb, .jump hb⟩) ls2 :=
        ⟨⟨⟨[], #[]⟩, by rw [setCur_blocks hs1]; exact hbjb, rfl⟩, carried.2⟩
      have generatedF := (generated.lowerExpr c h1).fork cv hf
      have generated2 := generatedF.setCur (some tb)
        (by intro current same; cases same; exact (Array.getElem?_eq_some_iff.mp hbtb).1) hs1
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
      cases residual with
      | zero => exact FuelBoundAt.zero sourceFuel cx pt1 fr1 _ _ afterCond
      | succ branchFuel =>
        have branchBound : branchFuel < fuel := by omega
        cases β
        · simp only [Bool.false_eq_true,↓reduceIte]
          refine FuelBoundAt.condbr hinst' hcv hTtb hTtbp hTjb hTjbp ?_
          exact FuelBoundAt.ret (sourceFuel := sourceFuel) (targetFuel := branchFuel) (Or.inl ⟨rfl,Post.nil hpp' hmono P1.same
            (P1.rel.stack_eq (by rw [hstl,hst1]))⟩)
        · simp only [↓reduceIte]
          refine FuelBoundAt.condbr hinst' hcv hTtb hTtbp hTjb hTjbp ?_
          have hcontextDepth : ls1.stack.length = env.scopes.length := by
            rw [P1.rel.stack,List.length_map]
          obtain ⟨bodySource,bodyTyping,bodyRoots,_,_⟩ := source.whileBodyChild sourceFuel hactualCond
          have bodyMetadata : SourceResults bodySource.typingEnv bodySource.rootsEnv results := by
            apply metadata.transport
            · rw [bodyTyping]
            · rw [bodyRoots]
          have bodyLoops : LoopSourceMatches bodySource.typingEnv (some ⟨ls1.stack.length,jb,.jump hb⟩) := by
            rw [LoopSourceMatches,bodyTyping]
            simp
          have bodyReflection := blocks branchFuel branchBound ⟨ls1.stack.length,jb,.jump hb⟩ env afterCond
            bodySource bodyMetadata bodyLoops ls2 ls3 vt (tb,0) cx fr1 ha1 hpp2 hext3 hrel2 (by trivial)
            moduleEq resultsEq (by change ls1.stack.length ≤ env.scopes.length; omega)
            ⟨⟨Tjb,hTjb,hTjbp⟩,hheader⟩ (by trivial) generated2 bodyFrames
          rw [prepareLoopFlow_at_depth env _ hcontextDepth] at bodyReflection
          refine bodyReflection.bind ?_
          · intro flow afterBody pt3 fr3 hactualBody hpost remaining remainingBound
            rcases hpost with ⟨v,hf,_,P3⟩ | ⟨returned,returnOrg,hf,hsite⟩ | ⟨context,hloop,htransfer⟩
            · subst hf
              simp only [returnWhileTail]
              obtain ⟨_,_,_,hi3'⟩ := emitTerm_facts ht P3.pp hext4
              obtain ⟨Thb,hThb,hThbp⟩ := hheader
              have hi3 : instAt cx.fn pt3 = some (.term (.br hb [])) := hi3'
              have hst3 : ls3.stack = ls.stack := P3.rel.stack.trans hrel.stack.symm
              have hrelH : Rel cfg env cx fr3 ls := P3.rel.stack_eq hst3.symm
              cases remaining with
              | zero => exact FuelBoundAt.zero sourceFuel cx pt3 fr3 _ _ afterBody
              | succ nextFuel =>
                have nextBound : nextFuel < fuel := by omega
                have rawBody := preparedReturn_nonreturn_success hactualBody (by intro value impossible; cases impossible)
                obtain ⟨next,nextTyping,nextRoots,_,_⟩ := source.whileAfterBody sourceFuel sourceFuel (.normal v)
                  hactualCond rawBody (Or.inl ⟨v,rfl⟩)
                have nextMetadata : SourceResults next.typingEnv next.rootsEnv results := by
                  rw [nextTyping,nextRoots]
                  exact metadata
                refine FuelBoundAt.br0 hi3 hThb hThbp ((reentry nextFuel nextBound env afterBody next nextMetadata
                  ls ls' hb cx fr3 hlow0 hpp hext ⟨Thb,hThb,hThbp⟩ hrelH moduleEq resultsEq generated).mono ?_)
                intro flow final pt' fr' matched
                rcases matched with ⟨hflow,P⟩ | hreturned
                · refine Or.inl ⟨hflow,⟨P.pp,P.has,P.lt,P.mono,?_,P.rel⟩⟩
                  have hsame : Same ls.vals.size fr fr3 :=
                    P1.same.trans (P3.same.mono (by rw [hv2]; exact hm1)) (Nat.le_refl _)
                  exact hsame.trans P.same (Nat.le_refl _)
                · exact Or.inr hreturned
            · subst hf
              exact FuelBoundAt.ret (sourceFuel := sourceFuel) (targetFuel := remaining) (Or.inr ⟨returned,returnOrg,rfl,hsite⟩)
            · obtain rfl := Option.some.inj hloop
              rcases htransfer with ⟨rfl,hpoint,hframe⟩ | ⟨rfl,hcontinue⟩
              · change pt3 = (jb,0) at hpoint
                subst pt3
                have hscopes : fr3.scopes = env.scopes := by
                  simpa only [hcontextDepth,Nat.sub_self,List.drop_zero] using hframe.scopesEqual
                have hrelExit : Rel cfg env cx fr3 ls' :=
                  ⟨hrel.prof,hrel.slots,hframe.activation.trans hrel2.act,hscopes,
                    hframe.depth.trans hrel2.depth,hstl.trans hrel.stack⟩
                have hsame : Same ls.vals.size fr fr3 :=
                  P1.same.trans (hframe.values.mono (by rw [hv2]; exact P1.mono)) (Nat.le_refl _)
                exact FuelBoundAt.ret (sourceFuel := sourceFuel) (targetFuel := remaining) (Or.inl ⟨rfl,Post.nil hpp' hmono hsame hrelExit⟩)
              · change pt3 = (hb,0) ∧ LoopFramePost fr1 ls2.vals.size
                  (env.scopes.drop (env.scopes.length - ls1.stack.length)) fr3 at hcontinue
                obtain ⟨rfl,hframe⟩ := hcontinue
                have hscopes : fr3.scopes = env.scopes := by
                  simpa only [hcontextDepth,Nat.sub_self,List.drop_zero] using hframe.scopesEqual
                have hrelH : Rel cfg env cx fr3 ls :=
                  ⟨hrel.prof,hrel.slots,hframe.activation.trans hrel2.act,hscopes,
                    hframe.depth.trans hrel2.depth,hrel.stack⟩
                have hsame : Same ls.vals.size fr fr3 :=
                  P1.same.trans (hframe.values.mono (by rw [hv2]; exact P1.mono)) (Nat.le_refl _)
                have nextBound : remaining < fuel := by omega
                have rawBody := preparedReturn_nonreturn_success hactualBody (by intro value impossible; cases impossible)
                obtain ⟨next,nextTyping,nextRoots,_,_⟩ := source.whileAfterBody sourceFuel sourceFuel .cont
                  hactualCond rawBody (Or.inr rfl)
                have nextMetadata : SourceResults next.typingEnv next.rootsEnv results := by
                  rw [nextTyping,nextRoots]
                  exact metadata
                exact (reentry remaining nextBound env afterBody next nextMetadata ls ls' hb cx fr3 hlow0 hpp
                  hext hheader hrelH moduleEq resultsEq generated).mono (fun flow final pt' fr' matched => by
                    rcases matched with ⟨hflow,P⟩ | returned
                    · exact Or.inl ⟨hflow,⟨P.pp,P.has,P.lt,P.mono,hsame.trans P.same (Nat.le_refl _),P.rel⟩⟩
                    · exact Or.inr returned)
  exact composition.of_source (otherFuel := sourceFuel + 1)
    (congrFun (prepareReturn_execWhile sourceFuel cfg env c body) state)

theorem typedStatementFuelBound_while {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {lc : Option LoopCtx} {c : Expr} {body : Core.Block} {org : OriginId}
    (loopsReflection : ∀ residual, residual < fuel → TypedWhileFuelBound sourceFuel residual cfg results c body org) :
    TypedStatementFuelBound (sourceFuel + 1) fuel cfg results lc (.while c body org) := by
  intro env state source metadata loops ls ls' pt cx fr hlow hpp hext hrel moduleEq resultsEq depth targets
    counter generated frames
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨⟨hb, ps⟩, ls1, hn, u1, ls2, ht, u2, lsH, hs, hw⟩ := hlow
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
  have generated1 := generated.newBlock [] hn
  have generated2 := generated1.emitTerm (.br hb [])
    (by
      intro target member
      simp only [Term.successors, List.mem_singleton] at member
      subst target
      exact (Array.getElem?_eq_some_iff.mp hnew).1) ht
  have generatedH := generated2.setCur (some hb)
    (by intro current same; cases same; exact (Array.getElem?_eq_some_iff.mp hb2).1) hs
  have hi : instAt cx.fn pt = some (.term (.br hb [])) := hinst
  cases fuel with
  | zero => exact FuelBoundAt.zero (sourceFuel + 1) cx pt fr _ _ state
  | succ fuel =>
    have reflection : FuelBoundAt sourceFuel (fuel + 1) cx pt fr
        (fun n => execWhile n cfg env c body >>= prepareReturn env)
        (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr ls' lc flow pt' fr') state := by
      refine FuelBoundAt.br0 hi hThb hThbp
        ((loopsReflection fuel (by omega) env state source metadata lsH ls' hb cx fr hw hppH hext
          ⟨Thb,hThb,hThbp⟩ hrelH moduleEq resultsEq generatedH).mono ?_)
      intro flow after pt' fr' matched
      rcases matched with ⟨hflow,P⟩ | returned
      · refine Or.inl ⟨hflow,⟨P.pp,P.has,P.lt,?_,?_,P.rel⟩⟩
        · rw [← hsizeH]; exact P.mono
        · rw [← hsizeH]; exact P.same
      · exact Or.inr (Or.inl returned)
    refine reflection.of_source (otherFuel := sourceFuel + 1) ?_
    simp only [execStmt,prepareLoopFlow_execWhile]

#print axioms typedWhileFuelBound_step
#print axioms typedStatementFuelBound_while

end Goose.Lower

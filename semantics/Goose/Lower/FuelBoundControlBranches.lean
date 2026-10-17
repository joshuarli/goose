import Goose.Lower.FuelBoundControlSteps
import Goose.Lower.FuelBoundTyped
import Goose.Lower.FuelBoundBlocks
import Goose.Lower.TypedControlExpressions

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem typedExprFuelBound_ifE {n fuel : Nat} {cfg : Cfg} {results : List Ty} {cond : Expr}
    {thenBlock elseBlock : Core.Block} (conditionClaim : TypedExprFuelBound n fuel cfg results cond)
    (thenClaim : ∀ residual, residual ≤ fuel → TypedBlockFuelBound n residual cfg results none [] [] true thenBlock)
    (elseClaim : ∀ residual, residual ≤ fuel → TypedBlockFuelBound n residual cfg results none [] [] true elseBlock) :
    TypedExprFuelBound (n + 2) fuel cfg results (.ifE cond thenBlock elseBlock) := by
  intro env state source metadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults generated
  obtain ⟨condition,conditionTyping,conditionRoots,conditionType,_⟩ := source.ifEChildren 0
  have conditionMetadata : SourceResults condition.typingEnv condition.rootsEnv results := by
    rw [conditionTyping,conditionRoots]; exact metadata
  let le := lowerEnv cfg.mod env.vars results
  simp only [lowerExpr,bind_eq] at hlow
  obtain ⟨cv,ls1,h1,hw⟩ := hlow
  have hadv_w := advB_ifE_core cv (advB_lowerBlock none [] true thenBlock)
    (advB_lowerBlock none [] true elseBlock) _ _ _ _ hw
  have hext1 := hext.of_adv hadv_w
  have first := conditionClaim env state condition conditionMetadata ls ls1 cv pt cx fr h1 hpp hext1
    hrel hgir hresults generated
  have composition : FuelBoundAt (n + 1) fuel cx pt fr
      (fun n => evalExpr n cfg env cond >>= fun value => expectBool value >>= fun selected =>
        blockValue n cfg env (if selected then thenBlock else elseBlock))
      (fun value _ pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r,.val value)]) state := by
    refine (first.source_mono
      (fun n k bound => (monoAll n k bound).expr cfg env cond) (Nat.le_succ n)).bind ?_
    · intro va afterCondition pt1 fr1 hdone P1 branchFuel branchBound
      have typed := (condition.result (n + 1) va hdone).typed
      rw [conditionType] at typed
      obtain ⟨selected,rfl⟩ := Core.Sound.hasTy_bool typed
      simp only [expectBool,pure_bind]
      obtain ⟨_,_,_,_,next⟩ := source.ifEChildren (n + 1)
      obtain ⟨body,bodyTyping,bodyRoots⟩ := next selected afterCondition hdone
      have bodyMetadata : SourceResults body.typingEnv body.rootsEnv results := by
        rw [bodyTyping,bodyRoots]; simpa [SourceResults,exprEnv] using metadata
      have bodyLoops : body.typingEnv.loops = 0 := by simp [bodyTyping,exprEnv]
      have bodyInExpr : body.typingEnv.inExpr = true := by simp [bodyTyping,exprEnv]
      have hcv : fr1.vals[cv]? = some (.val (.bool selected)) := P1.has (cv,_) (by simp)
      obtain ⟨blk1,hc1,hb1,hp1⟩ := LS.pp_some P1.pp
      rw [whenLive_some _ _ _ hc1] at hw
      simp only [bind_eq] at hw
      obtain ⟨⟨tb,eb⟩,lsf,hf,u2,ls2,hs1,vt,ls3,ha1,endT,ls4,hc4,u5,ls5,hs2,vf,ls6,ha2,
        endF,ls7,hc7,hj⟩ := hw
      cases u2
      cases u5
      obtain ⟨e4c,e4⟩ := curBlock_eq hc4
      subst e4
      obtain ⟨e7c,e7⟩ := curBlock_eq hc7
      subst e7
      have hext6 := hext.of_ext (joinValue_ext hj)
      have hadv1 := advB_lowerBlock none [] true thenBlock _ _ _ _ ha1
      have hadv2 := advB_lowerBlock none [] true elseBlock _ _ _ _ ha2
      obtain ⟨htb,heb,hinst,⟨Ttb,hTtb,hTtbp⟩,⟨Teb,hTeb,hTebp⟩,hpp2,hpp5,hst2,hv2,hst3,hst6,
        hv16,hv36,hendT,hendF,hkeep,hsz36,hsz6⟩ :=
        branch_facts hf hs1 hadv1 hs2 hadv2 P1.pp hext6
      have hrel2 := P1.rel.stack_eq hst2
      have hltT : ∀ b, endT = some b → b < ls7.blocks.size := by
        intro b hb
        exact Nat.lt_of_lt_of_le (hendT b (by rw [e4c] at hb; exact hb)).1 hsz36
      have hltF : ∀ b, endF = some b → b < ls7.blocks.size := by
        intro b hb
        exact (hendF b (by rw [e7c] at hb; exact hb)).1
      have hnd : ∀ bT bF, endT = some bT → endF = some bF → bT ≠ bF := by
        intro bT bF hT hF
        obtain ⟨hlt,hne,hcase⟩ := hendT bT (by rw [e4c] at hT; exact hT)
        obtain ⟨_,hcase'⟩ := hendF bF (by rw [e7c] at hF; exact hF)
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
      have genF := (generated.lowerExpr cond h1).fork cv hf
      have forkSize := (fork_ids hf).2
      have genT := genF.setCur (some tb)
        (by intro current equal; have same := Option.some.inj equal; rw [← same,htb,forkSize]; nat_omega) hs1
      have gen4 := genT.lowerBlock none [] true thenBlock trivial ha1
      have e2 : ls2 = { lsf with cur := some tb } := by
        rw [setCur_run] at hs1; exact (Prod.mk.inj hs1).2.symm
      have genE := gen4.setCur (some eb)
        (by intro current equal; have same := Option.some.inj equal; rw [← same,heb]
            have bound := hadv1.ext.1
            rw [e2] at bound
            nat_omega) hs2
      cases branchFuel with
      | zero => exact FuelBoundAt.zero (n + 1) _ _ _ _ _ _
      | succ branchFuel =>
        cases selected
        · simp only [Bool.false_eq_true,↓reduceIte]
          have hrel5 := P1.rel.stack_eq (show ls5.stack = ls1.stack by rw [e5]; exact hst3)
          have branchReflection := (elseClaim branchFuel (by nat_omega)).value env afterCondition body bodyMetadata
            bodyLoops bodyInExpr ls5 ls7 vf (eb,0) cx fr1 ha2 hpp5 hext6 hrel5 hgir hresults genE
          have joined : FuelBoundAt (n + 1) branchFuel cx (eb,0) fr1 (fun n => blockValue n cfg env elseBlock)
              (fun v _ pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r,.val v)]) afterCondition := by
            have bindJoin : FuelBoundAt (n + 1) branchFuel cx (eb,0) fr1
                (fun n => blockValue n cfg env elseBlock >>= pure)
                (fun v _ pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r,.val v)]) afterCondition := by
              refine branchReflection.bind ?_
              intro v finalState pt7 fr7 blockDone P7 joinFuel joinBound
              obtain ⟨blk7,hc7',hb7,hp7⟩ := LS.pp_some P7.pp
              have hendF' : endF = some pt7.1 := by rw [e7c]; exact hc7'
              have hlive : endT.isSome ∨ endF.isSome := Or.inr (by rw [hendF']; rfl)
              obtain ⟨ty,hr,hvj,hstj,hbj,hcj,hTj,hFj⟩ := joinValue_facts hj hext hlive hnd hltT hltF
              have hinstF := hFj pt7.1 blk7 hendF' hb7
              obtain ⟨Tjb,hTjb,hTjbp⟩ := hext.params hbj
              have hcell := P7.has (vf,.val v) (by simp)
              have hpt7 : pt7 = (pt7.1,blk7.insts.size) := Prod.ext rfl hp7
              have hi7 : instAt cx.fn pt7 = some (.term (.br ls7.blocks.size [vf])) := by
                rw [hpt7]; exact hinstF
              cases joinFuel with
              | zero => exact FuelBoundAt.zero (n + 1) _ _ _ _ _ _
              | succ joinFuel =>
                apply FuelBoundAt.br1 hi7 hTjb hTjbp hcell
                apply FuelBoundAt.ret
                rw [hr]
                have hsame : Same ls.vals.size fr fr7 := by
                  refine P1.same.trans (P7.same.mono ?_) P1.mono
                  rw [e5]; exact hmono_all
                exact Post.join hsame (P7.rel.stack_eq (hrel.stack.trans P7.rel.stack.symm))
                  (by nat_omega) (by nat_omega) (by nat_omega) (hstj.trans hst_out) (LS.pp_eq hcj hbj)
            simpa only [bind_pure] using bindJoin
          exact FuelBoundAt.condbr_take0 hinst' hcv hTeb hTebp rfl joined
        · simp only [↓reduceIte]
          have branchReflection := (thenClaim branchFuel (by nat_omega)).value env afterCondition body bodyMetadata
            bodyLoops bodyInExpr ls2 ls4 vt (tb,0) cx fr1 ha1 hpp2 hext4 hrel2 hgir hresults genT
          have joined : FuelBoundAt (n + 1) branchFuel cx (tb,0) fr1 (fun n => blockValue n cfg env thenBlock)
              (fun v _ pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r,.val v)]) afterCondition := by
            have bindJoin : FuelBoundAt (n + 1) branchFuel cx (tb,0) fr1
                (fun n => blockValue n cfg env thenBlock >>= pure)
                (fun v _ pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r,.val v)]) afterCondition := by
              refine branchReflection.bind ?_
              intro v finalState pt3 fr3 blockDone P3 joinFuel joinBound
              obtain ⟨blk3,hc3,hb3,hp3⟩ := LS.pp_some P3.pp
              have hendT' : endT = some pt3.1 := by rw [e4c]; exact hc3
              have hlive : endT.isSome ∨ endF.isSome := Or.inl (by rw [hendT']; rfl)
              obtain ⟨ty,hr,hvj,hstj,hbj,hcj,hTj,hFj⟩ := joinValue_facts hj hext hlive hnd hltT hltF
              have hne : pt3.1 ≠ eb := (hendT pt3.1 hc3).2.1
              have hb7 := hkeep pt3.1 blk3 hb3 hne
              have hinstT := hTj pt3.1 blk3 hendT' hb7
              obtain ⟨Tjb,hTjb,hTjbp⟩ := hext.params hbj
              have hcell := P3.has (vt,.val v) (by simp)
              have hpt3 : pt3 = (pt3.1,blk3.insts.size) := Prod.ext rfl hp3
              have hi3 : instAt cx.fn pt3 = some (.term (.br ls7.blocks.size [vt])) := by
                rw [hpt3]; exact hinstT
              cases joinFuel with
              | zero => exact FuelBoundAt.zero (n + 1) _ _ _ _ _ _
              | succ joinFuel =>
                apply FuelBoundAt.br1 hi3 hTjb hTjbp hcell
                apply FuelBoundAt.ret
                rw [hr]
                have hsame : Same ls.vals.size fr fr3 := by
                  refine P1.same.trans (P3.same.mono ?_) P1.mono
                  nat_omega
                exact Post.join hsame (P3.rel.stack_eq (hrel.stack.trans P3.rel.stack.symm))
                  (by nat_omega) (by nat_omega) (by nat_omega) (hstj.trans hst_out) (LS.pp_eq hcj hbj)
            simpa only [bind_pure] using bindJoin
          exact FuelBoundAt.condbr_take0 hinst' hcv hTtb hTtbp rfl joined
  exact composition.of_source (otherFuel := n + 2) (by
    simp only [evalExpr]
    apply congrArg (fun action : M Val => action state)
    congr 1
    funext value
    congr 1
    funext selected
    cases selected <;> rfl)


#print axioms typedExprFuelBound_ifE

end Goose.Lower

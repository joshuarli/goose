import Goose.Lower.ReflectionBlocks
import Goose.Lower.ReflectionBranchesSteps
import Goose.Lower.TypedControlExpressions

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem TypedBlockReflection.value {fuel : Nat} {cfg : Cfg} {results : List Ty} {block : Core.Block}
    (reflection : TypedBlockReflection fuel cfg results none [] [] true block)
    (env : Env) (state : St) (source : BlockSource cfg env [] block state)
    (metadata : SourceResults source.typingEnv source.rootsEnv results)
    (loops : source.typingEnv.loops = 0) (inExpr : source.typingEnv.inExpr = true)
    (ls after : LS) (result : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame)
    (lowering : lowerBlock none [] true block (lowerEnv cfg.mod env.vars results) ls = (result,after))
    (point : ls.pp = some pt) (extension : ExtT after cx.fn.blocks) (rel : Rel cfg env cx fr ls)
    (moduleEq : cx.cfg.mod = lower cfg.mod) (resultsEq : cx.fn.results = results)
    (generated : GeneratedBuilderState ls) :
    ReflectAtFuel fuel cx pt fr (fun n => blockValue n cfg env block)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(result,.val value)]) state := by
  have whole := reflection.function env state source metadata loops ls after result pt cx fr lowering
    point extension rel trivial moduleEq resultsEq generated
  have prepareEq (n : Nat) : (execBlock n cfg env [] block >>= prepareReturn env) state =
      execBlock n cfg env [] block state := by
    rw [bind_apply]
    cases done : execBlock n cfg env [] block state with
    | stop reason final => rfl
    | ok flow final =>
      obtain ⟨value,rfl⟩ := source.expressionFlow n flow loops inExpr done
      rfl
  have raw := whole.of_source (other := fun n => execBlock n cfg env [] block)
    (fun n => ⟨n,(prepareEq n).symm⟩)
  have extracted : ReflectAtFuel fuel cx pt fr
      (fun n => execBlock n cfg env [] block >>= expectNormal)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(result,.val value)]) state := by
    refine raw.bind ?_ (fun n k le => (monoAll n k le).block cfg env [] block)
      (fun _ _ _ _ => MonoM.refl _)
    intro n flow next pt' fr' done matched residual bound
    obtain ⟨value,rfl⟩ := source.expressionFlow n flow loops inExpr done
    rcases matched with ⟨normal,same,unit,post⟩ | ⟨returned,origin,same,site⟩
    · cases same
      exact ReflectAtFuel.ret residual (by simpa [blockCells] using post)
    · cases same
  exact extracted.of_source (fun n => ⟨n + 1,by simp only [blockValue]⟩)

theorem typedExprReflection_blockE {fuel : Nat} {cfg : Cfg} {results : List Ty} {block : Core.Block}
    (body : TypedBlockReflection fuel cfg results none [] [] true block) :
    TypedExprReflection fuel cfg results (.blockE block) := by
  intro env state source metadata ls after result pt cx fr lowering point extension rel moduleEq
    resultsEq generated
  obtain ⟨child,typing,roots⟩ := source.blockEChild
  have childMetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [typing,roots]
    simpa [SourceResults,exprEnv] using metadata
  simp only [lowerExpr] at lowering
  have value := body.value env state child childMetadata (by simp [typing,exprEnv])
    (by simp [typing,exprEnv]) ls after result pt cx fr lowering point extension rel moduleEq resultsEq generated
  exact value.of_source (fun n => ⟨n + 1,by simp only [evalExpr]⟩)

theorem typedExprReflection_ifE {fuel : Nat} {cfg : Cfg} {results : List Ty} {cond : Expr}
    {thenBlock elseBlock : Core.Block} (conditionClaim : TypedExprReflection fuel cfg results cond)
    (thenClaim : ∀ residual, residual ≤ fuel → TypedBlockReflection residual cfg results none [] [] true thenBlock)
    (elseClaim : ∀ residual, residual ≤ fuel → TypedBlockReflection residual cfg results none [] [] true elseBlock) :
    TypedExprReflection fuel cfg results (.ifE cond thenBlock elseBlock) := by
  intro env state source metadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults generated
  obtain ⟨condition,conditionTyping,conditionRoots,conditionType,_⟩ := source.ifEChildren 0
  have conditionMetadata : SourceResults condition.typingEnv condition.rootsEnv results := by
    rw [conditionTyping,conditionRoots]; exact metadata
  let le := lowerEnv cfg.mod env.vars results
  simp only [lowerExpr,bind_eq] at hlow
  obtain ⟨cv,ls1,h1,hw⟩ := hlow
  have hadv_w := advB_ifE_core cv (sourceBlockScope thenBlock)
    (advB_lowerBlock none [] true thenBlock) (advB_lowerBlock none [] true elseBlock) _ _ _ _ hw
  have hext1 := hext.of_adv hadv_w
  have first := conditionClaim env state condition conditionMetadata ls ls1 cv pt cx fr h1 hpp hext1
    hrel hgir hresults generated
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalExpr n cfg env cond >>= fun value => expectBool value >>= fun selected =>
        blockValue n cfg env (if selected then thenBlock else elseBlock))
      (fun value _ pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r,.val value)]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env cond) ?_
    · intro n va afterCondition pt1 fr1 hdone P1 branchFuel branchBound
      have typed := (condition.result n va hdone).typed
      rw [conditionType] at typed
      obtain ⟨selected,rfl⟩ := Core.Sound.hasTy_bool typed
      simp only [expectBool,pure_bind]
      obtain ⟨_,_,_,_,next⟩ := source.ifEChildren n
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
        endF,ls7,hc7,joined,ls8,hj,u8,ls9,hrecipe,hpure⟩ := hw
      cases u2
      cases u5
      obtain ⟨e4c,e4⟩ := curBlock_eq hc4
      subst e4
      obtain ⟨e7c,e7⟩ := curBlock_eq hc7
      subst e7
      rw [pure_run] at hpure
      have hfinal : ls9 = ls' := (Prod.mk.inj hpure).2
      have recipeExt : ls8.Ext ls9 :=
        (advB_recordValueRootRecipe joined (sourceBlockScope thenBlock) _ _ _ _ hrecipe).ext
      have recipeState := hrecipe
      rw [recordValueRootRecipe_run] at recipeState
      have recipeUpdate := (Prod.mk.inj recipeState).2
      have recipeVals : ls9.vals = ls8.vals := by
        simpa using (congrArg LS.vals recipeUpdate).symm
      have recipeStack : ls9.stack = ls8.stack := by
        simpa using (congrArg LS.stack recipeUpdate).symm
      have recipePp : ls8.pp = ls9.pp := by
        simpa [LS.pp] using congrArg LS.pp recipeUpdate
      have recipeFinal : ls8.Ext ls' := by
        rw [← hfinal]
        exact recipeExt
      have finalVals : ls'.vals = ls8.vals := by
        rw [← hfinal]
        exact recipeVals
      have finalStack : ls'.stack = ls8.stack := by
        rw [← hfinal]
        exact recipeStack
      have joinOutputExt : ExtT ls8 cx.fn.blocks := hext.of_ext recipeFinal
      have hext6 := joinOutputExt.of_ext (joinValue_ext hj)
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
      | zero => exact ReflectAtFuel.zero _ _ _ _ _ _
      | succ branchFuel =>
        cases selected
        · simp only [Bool.false_eq_true,↓reduceIte]
          have hrel5 := P1.rel.stack_eq (show ls5.stack = ls1.stack by rw [e5]; exact hst3)
          have branchReflection := (elseClaim branchFuel (by nat_omega)).value env afterCondition body bodyMetadata
            bodyLoops bodyInExpr ls5 ls7 vf (eb,0) cx fr1 ha2 hpp5 hext6 hrel5 hgir hresults genE
          have joined : ReflectAtFuel branchFuel cx (eb,0) fr1 (fun n => blockValue n cfg env elseBlock)
              (fun v _ pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r,.val v)]) afterCondition := by
            have bindJoin : ReflectAtFuel branchFuel cx (eb,0) fr1
                (fun n => blockValue n cfg env elseBlock >>= pure)
                (fun v _ pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r,.val v)]) afterCondition := by
              refine branchReflection.bind ?_ (fun n k le => (monoAll n k le).blockValue cfg env elseBlock)
                (fun _ _ _ _ => MonoM.refl _)
              intro n v finalState pt7 fr7 blockDone P7 joinFuel joinBound
              obtain ⟨blk7,hc7',hb7,hp7⟩ := LS.pp_some P7.pp
              have hendF' : endF = some pt7.1 := by rw [e7c]; exact hc7'
              have hlive : endT.isSome ∨ endF.isSome := Or.inr (by rw [hendF']; rfl)
              obtain ⟨ty,hr,hvj,hstj,hbj,hcj,hTj,hFj⟩ := joinValue_facts hj joinOutputExt hlive hnd hltT hltF
              have hresult : r = ls7.vals.size := (Prod.mk.inj hpure).1.symm.trans hr
              have finalPp : ls'.pp = some (ls7.blocks.size, 0) := by
                rw [← hfinal, ← recipePp]
                exact LS.pp_eq hcj hbj
              have hinstF := hFj pt7.1 blk7 hendF' hb7
              obtain ⟨Tjb,hTjb,hTjbp⟩ := joinOutputExt.params hbj
              have hcell := P7.has (vf,.val v) (by simp)
              have hpt7 : pt7 = (pt7.1,blk7.insts.size) := Prod.ext rfl hp7
              have hi7 : instAt cx.fn pt7 = some (.term (.br ls7.blocks.size [vf])) := by
                rw [hpt7]; exact hinstF
              cases joinFuel with
              | zero => exact ReflectAtFuel.zero _ _ _ _ _ _
              | succ joinFuel =>
                apply ReflectAtFuel.br1 hi7 hTjb hTjbp hcell
                apply ReflectAtFuel.ret joinFuel
                rw [hresult]
                have hsame : Same ls.vals.size fr fr7 := by
                  refine P1.same.trans (P7.same.mono ?_) P1.mono
                  rw [e5]; exact hmono_all
                exact Post.join hsame (P7.rel.stack_eq (hrel.stack.trans P7.rel.stack.symm))
                  (by nat_omega) (by rw [finalVals]; nat_omega) (by rw [finalVals]; nat_omega)
                  (finalStack.trans (hstj.trans hst_out)) finalPp
            simpa only [bind_pure] using bindJoin
          exact ReflectAtFuel.condbr_take0 hinst' hcv hTeb hTebp rfl joined
        · simp only [↓reduceIte]
          have branchReflection := (thenClaim branchFuel (by nat_omega)).value env afterCondition body bodyMetadata
            bodyLoops bodyInExpr ls2 ls4 vt (tb,0) cx fr1 ha1 hpp2 hext4 hrel2 hgir hresults genT
          have joined : ReflectAtFuel branchFuel cx (tb,0) fr1 (fun n => blockValue n cfg env thenBlock)
              (fun v _ pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r,.val v)]) afterCondition := by
            have bindJoin : ReflectAtFuel branchFuel cx (tb,0) fr1
                (fun n => blockValue n cfg env thenBlock >>= pure)
                (fun v _ pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r,.val v)]) afterCondition := by
              refine branchReflection.bind ?_ (fun n k le => (monoAll n k le).blockValue cfg env thenBlock)
                (fun _ _ _ _ => MonoM.refl _)
              intro n v finalState pt3 fr3 blockDone P3 joinFuel joinBound
              obtain ⟨blk3,hc3,hb3,hp3⟩ := LS.pp_some P3.pp
              have hendT' : endT = some pt3.1 := by rw [e4c]; exact hc3
              have hlive : endT.isSome ∨ endF.isSome := Or.inl (by rw [hendT']; rfl)
              obtain ⟨ty,hr,hvj,hstj,hbj,hcj,hTj,hFj⟩ := joinValue_facts hj joinOutputExt hlive hnd hltT hltF
              have hresult : r = ls7.vals.size := (Prod.mk.inj hpure).1.symm.trans hr
              have finalPp : ls'.pp = some (ls7.blocks.size, 0) := by
                rw [← hfinal, ← recipePp]
                exact LS.pp_eq hcj hbj
              have hne : pt3.1 ≠ eb := (hendT pt3.1 hc3).2.1
              have hb7 := hkeep pt3.1 blk3 hb3 hne
              have hinstT := hTj pt3.1 blk3 hendT' hb7
              obtain ⟨Tjb,hTjb,hTjbp⟩ := joinOutputExt.params hbj
              have hcell := P3.has (vt,.val v) (by simp)
              have hpt3 : pt3 = (pt3.1,blk3.insts.size) := Prod.ext rfl hp3
              have hi3 : instAt cx.fn pt3 = some (.term (.br ls7.blocks.size [vt])) := by
                rw [hpt3]; exact hinstT
              cases joinFuel with
              | zero => exact ReflectAtFuel.zero _ _ _ _ _ _
              | succ joinFuel =>
                apply ReflectAtFuel.br1 hi3 hTjb hTjbp hcell
                apply ReflectAtFuel.ret joinFuel
                rw [hresult]
                have hsame : Same ls.vals.size fr fr3 := by
                  refine P1.same.trans (P3.same.mono ?_) P1.mono
                  nat_omega
                exact Post.join hsame (P3.rel.stack_eq (hrel.stack.trans P3.rel.stack.symm))
                  (by nat_omega) (by rw [finalVals]; nat_omega) (by rw [finalVals]; nat_omega)
                  (finalStack.trans (hstj.trans hst_out)) finalPp
            simpa only [bind_pure] using bindJoin
          exact ReflectAtFuel.condbr_take0 hinst' hcv hTtb hTtbp rfl joined
    · intro value n k bound
      exact (MonoM.refl _).bind (fun selected =>
        (monoAll n k bound).blockValue cfg env (if selected then thenBlock else elseBlock))
  exact composition.of_source (fun n => ⟨n + 1,by
    simp only [evalExpr]
    apply congrArg (fun action : M Val => action state)
    congr 1
    funext value
    congr 1
    funext selected
    cases selected <;> rfl⟩)

private theorem typed_shortCircuit_reflectAtFuel {fuel : Nat} {isAnd : Bool} {x : ValueId}
    {cfg : Cfg} {env : Env} {cx : FnCtx} {ls1 ls' : LS} {r : ValueId} {pt1 : Pt}
    {fr1 : Frame} {boolean : Bool} {state : St} {results : List Ty} {b : Expr}
    (right : ExprSource cfg env b state)
    (metadata : SourceResults right.typingEnv right.rootsEnv results) (type : right.ty = .bool)
    (child : ∀ residual, residual ≤ fuel → TypedExprReflection residual cfg results b)
    (hs : shortCircuit isAnd x (lowerExpr b) (lowerEnv cfg.mod env.vars results) ls1 = (r,ls'))
    (hpp : ls1.pp = some pt1) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr1 ls1)
    (hx : fr1.vals[x]? = some (.val (.bool boolean)))
    (moduleEq : cx.cfg.mod = lower cfg.mod) (resultsEq : cx.fn.results = results)
    (generated : GeneratedBuilderState ls1) :
    ReflectAtFuel fuel cx pt1 fr1 (fun n => if isAnd then
      if boolean then evalExpr n cfg env b >>= fun v => expectBool v >>= fun selected => pure (.bool selected)
        else pure (.bool false)
      else if boolean then pure (.bool true)
        else evalExpr n cfg env b >>= fun v => expectBool v >>= fun selected => pure (.bool selected))
      (fun v _ pt' fr' => Post cfg env cx ls1 fr1 ls' fr' pt' [(r,.val v)]) state := by
  obtain ⟨blk1, hc1, hb1, hp1⟩ := LS.pp_some hpp
  unfold shortCircuit at hs
  rw [whenLive_some _ _ _ hc1] at hs
  simp only [bind_eq] at hs
  obtain ⟨⟨rb, jb, p⟩, ls_c, h1, u2, ls_d, h2, y, ls_e, h3, u4, ls_f, h4, u5, ls_g, h5, hpure⟩ := hs
  rw [pure_run] at hpure
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpure
  have a_rhs : ls_d.Adv ls_e := advB_lowerExpr b _ _ _ _ h3
  have a_f := adv_emitTerm h4
  have hg : ls_g = { ls_f with cur := some jb } := by
    rw [setCur_run] at h5; exact (Prod.mk.inj h5).2.symm
  have hd : ls_d = { ls_c with cur := some rb } := by
    rw [setCur_run] at h2; exact (Prod.mk.inj h2).2.symm
  have hext_f : ExtT ls_f cx.fn.blocks := by rw [hg] at hext; exact hext
  have hext_e : ExtT ls_e cx.fn.blocks := hext_f.of_adv a_f
  have hext_d : ExtT ls_d cx.fn.blocks := hext_e.of_adv a_rhs
  have hext_c : ExtT ls_c cx.fn.blocks := by rw [hd] at hext_d; exact hext_d
  obtain ⟨hrb, hjb, hpv, hvc, hstc, hcurc, hinst, hbrb, hbjb⟩ := scFork_facts h1 hpp hext_c
  obtain ⟨-, hszc⟩ := scFork_ids h1
  cases u2
  cases u4
  cases u5
  subst hrb hjb hpv
  obtain ⟨Trb, hTrb, hTrbp⟩ := hext_c.params hbrb
  obtain ⟨Tjb, hTjb, hTjbp⟩ := hext_c.params hbjb
  have hdb : ls_d.blocks = ls_c.blocks := by rw [hd]
  have hdpp : ls_d.pp = some (ls1.blocks.size, 0) := by
    rw [hd]; exact LS.pp_cur hbrb
  have hstd : ls_d.stack = ls1.stack := by rw [hd]; exact hstc
  have hrel_d : Rel cfg env cx fr1 ls_d := hrel.stack_eq hstd
  have hvd : ls_d.vals.size = ls1.vals.size + 1 := by rw [hd]; exact hvc
  have hjb_d : ls_d.blocks[ls1.blocks.size + 1]? = some ⟨[(ls1.vals.size, .data .bool)], #[]⟩ := by
    rw [hdb]; exact hbjb
  have hjb_e : ls_e.blocks[ls1.blocks.size + 1]? = some ⟨[(ls1.vals.size, .data .bool)], #[]⟩ := by
    refine a_rhs.keep _ _ ?_ hjb_d
    rw [hd]
    intro hh
    have := Option.some.inj hh
    nat_omega
  have hjb_f : ls_f.blocks[ls1.blocks.size + 1]? = some ⟨[(ls1.vals.size, .data .bool)], #[]⟩ := by
    cases hce : ls_e.cur with
    | none =>
      rw [emitTerm_none _ _ hce] at h4
      obtain ⟨-, rfl⟩ := Prod.mk.inj h4
      exact hjb_e
    | some be =>
      rw [emitTerm_run _ _ hce] at h4
      obtain ⟨-, rfl⟩ := Prod.mk.inj h4
      have hbe : be ≠ ls1.blocks.size + 1 := by
        rcases a_rhs.cur with h | h | ⟨c, hc, hc1, _⟩
        · rw [hce] at h; cases h
        · rw [hce, hd] at h
          have := Option.some.inj h
          have hszd : ls_d.blocks.size = ls1.blocks.size + 2 := by rw [hdb]; exact hszc
          nat_omega
        · rw [hce] at hc
          have := Option.some.inj hc
          have hszd : ls_d.blocks.size = ls1.blocks.size + 2 := by rw [hdb]; exact hszc
          nat_omega
      show (ls_e.blocks.modify be _)[ls1.blocks.size + 1]? = _
      rw [getElem?_modify_ne hbe]
      exact hjb_e
  have hpp_g : ls_g.pp = some (ls1.blocks.size + 1, 0) := by
    rw [hg]; exact LS.pp_cur hjb_f
  have hst_g : ls_g.stack = ls1.stack := by
    rw [hg]
    show ls_f.stack = _
    rw [a_f.stack, a_rhs.stack, hstd]
  have hv_g : ls1.vals.size + 1 ≤ ls_g.vals.size := by
    rw [hg]
    show _ ≤ ls_f.vals.size
    have := a_f.vals; have := a_rhs.vals
    nat_omega
  have hmono : ls1.vals.size ≤ ls_g.vals.size := Nat.le_trans (Nat.le_succ _) hv_g
  have hlt : ls1.vals.size < ls_g.vals.size := hv_g
  have hTrb' : cx.fn.blocks[ls1.blocks.size]? = some Trb := hTrb
  have hTjb' : cx.fn.blocks[ls1.blocks.size + 1]? = some Tjb := hTjb
  have genC := generated.scFork isAnd x h1
  have genD := genC.setCur (some ls1.blocks.size)
    (by intro current equal; have same := Option.some.inj equal; rw [← same,hszc]; nat_omega) h2
  have rightReflection (residual : Nat) (bound : residual ≤ fuel) :=
    child residual bound env state right metadata ls_d ls_e y (ls1.blocks.size,0) cx fr1 h3 hdpp
      hext_e hrel_d moduleEq resultsEq genD
  have hjoin : ∀ (vb : Val) (pt_e : Pt) (fr_e : Frame),
      Post cfg env cx ls_d fr1 ls_e fr_e pt_e [(y,.val vb)] → ∀ selected, vb = .bool selected →
      ∀ (residual : Nat) (after : St), ReflectAtFuel residual cx pt_e fr_e
        (fun _ => pure (Val.bool selected)) (fun v _ pt' fr' =>
          Post cfg env cx ls1 fr1 ls_g fr' pt' [(ls1.vals.size,.val v)]) after := by
    intro vb pt_e fr_e P selected equal residual after
    subst vb
    obtain ⟨_,_,_,instruction⟩ := emitTerm_facts h4 P.pp hext_f
    have hy : fr_e.vals[y]? = some (.val (.bool selected)) := P.has (y,_) (by simp)
    cases residual with
    | zero => exact ReflectAtFuel.zero _ _ _ _ _ _
    | succ residual =>
      apply ReflectAtFuel.br1 instruction hTjb' hTjbp hy
      apply ReflectAtFuel.ret residual
      have same : Same ls1.vals.size fr1 fr_e := P.same.mono (by nat_omega)
      have rel : Rel cfg env cx fr_e ls1 := P.rel.stack_eq (by rw [a_rhs.stack,hstd])
      exact Post.join same rel (Nat.le_refl _) hlt hmono hst_g hpp_g
  have rightJoin (residual : Nat) (bound : residual ≤ fuel) : ReflectAtFuel residual cx
      (ls1.blocks.size,0) fr1
      (fun n => evalExpr n cfg env b >>= fun v => expectBool v >>= fun selected => pure (.bool selected))
      (fun v _ pt' fr' => Post cfg env cx ls1 fr1 ls_g fr' pt' [(ls1.vals.size,.val v)]) state := by
    refine (rightReflection residual bound).bind ?_
      (fun n k bound => (monoAll n k bound).expr cfg env b) (fun _ _ _ _ => MonoM.refl _)
    intro n vb after pt_e fr_e done P joinFuel joinBound
    have typed := (right.result n vb done).typed
    rw [type] at typed
    obtain ⟨selected,rfl⟩ := Core.Sound.hasTy_bool typed
    simp only [expectBool,pure_bind]
    exact hjoin (.bool selected) pt_e fr_e P selected rfl joinFuel after
  have shortPost (selected : Bool) :
      Post cfg env cx ls1 fr1 ls_g (fr1.set ls1.vals.size (.val (.bool selected)))
        (ls1.blocks.size + 1,0) [(ls1.vals.size,.val (.bool selected))] :=
    Post.join (Same.refl _ _) hrel (Nat.le_refl _) hlt hmono hst_g hpp_g
  cases fuel with
  | zero => exact ReflectAtFuel.zero _ _ _ _ _ _
  | succ fuel =>
    cases isAnd <;> cases boolean
    · have hi : instAt cx.fn pt1 = some
          (.term (.condbr x (ls1.blocks.size + 1) [x] ls1.blocks.size [])) := hinst
      exact ReflectAtFuel.condbr_take0 hi hx hTrb' hTrbp rfl (rightJoin fuel (by omega))
    · have hi : instAt cx.fn pt1 = some
          (.term (.condbr x (ls1.blocks.size + 1) [x] ls1.blocks.size [])) := hinst
      exact ReflectAtFuel.condbr_take1 hi hx hTjb' hTjbp rfl hx (ReflectAtFuel.ret fuel (shortPost true))
    · have hi : instAt cx.fn pt1 = some
          (.term (.condbr x ls1.blocks.size [] (ls1.blocks.size + 1) [x])) := hinst
      exact ReflectAtFuel.condbr_take1 hi hx hTjb' hTjbp rfl hx (ReflectAtFuel.ret fuel (shortPost false))
    · have hi : instAt cx.fn pt1 = some
          (.term (.condbr x ls1.blocks.size [] (ls1.blocks.size + 1) [x])) := hinst
      exact ReflectAtFuel.condbr_take0 hi hx hTrb' hTrbp rfl (rightJoin fuel (by omega))

private theorem typedExprReflection_shortCircuit {fuel : Nat} {cfg : Cfg} {results : List Ty}
    {a b : Expr} (leftClaim : TypedExprReflection fuel cfg results a)
    (rightClaim : ∀ residual, residual ≤ fuel → TypedExprReflection residual cfg results b) (isAnd : Bool) :
    TypedExprReflection fuel cfg results (if isAnd then .and a b else .or a b) := by
  let tail (cfg : Cfg) (env : Env) (n : Nat) (boolean : Bool) : M Val := if isAnd then
    if boolean then evalExpr n cfg env b >>= fun v => expectBool v >>= fun selected => pure (.bool selected)
      else pure (.bool false)
    else if boolean then pure (.bool true)
      else evalExpr n cfg env b >>= fun v => expectBool v >>= fun selected => pure (.bool selected)
  cases isAnd
  all_goals
    intro env state source metadata ls ls' r pt cx fr lowering point extension rel moduleEq resultsEq generated
    obtain ⟨left,typing,roots,type,next⟩ := source.shortCircuitChildren _
    have leftMetadata : SourceResults left.typingEnv left.rootsEnv results := by
      rw [typing,roots]; exact metadata
    simp only [Bool.false_eq_true,ite_false,ite_true,lowerExpr,bind_eq] at lowering
    obtain ⟨x,first,firstRun,shortRun⟩ := lowering
    have firstExtension := extension.of_adv (advB_shortCircuit _ x (advB_lowerExpr b) _ _ _ _ shortRun)
    have firstReflection := leftClaim env state left leftMetadata ls first x pt cx fr firstRun point
      firstExtension rel moduleEq resultsEq generated
    have genFirst := generated.lowerExpr a firstRun
    have composition : ReflectAtFuel fuel cx pt fr
        (fun n => evalExpr n cfg env a >>= fun value => expectBool value >>= fun boolean =>
          tail cfg env n boolean) (fun v _ pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r,.val v)]) state := by
      refine firstReflection.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env a) ?_
      · intro n value after pt1 fr1 done P1 residual bound
        have typed := (left.result n value done).typed
        rw [type] at typed
        obtain ⟨boolean,rfl⟩ := Core.Sound.hasTy_bool typed
        simp only [expectBool,pure_bind]
        obtain ⟨right,rightTyping,rightRoots,rightType⟩ := next n (.bool boolean) after done
        have rightMetadata : SourceResults right.typingEnv right.rootsEnv results := by
          rw [rightTyping,rightRoots]; exact metadata
        have reflected := typed_shortCircuit_reflectAtFuel (boolean := boolean) right rightMetadata rightType
          (fun remaining remainingBound => rightClaim remaining (Nat.le_trans remainingBound bound))
          shortRun P1.pp extension P1.rel (P1.has (x,_) (by simp)) moduleEq resultsEq genFirst
        exact reflected.mono (fun v _ pt' fr' P => (P1.comp P).sub (by simp))
      · intro value n k bound
        refine (MonoM.refl _).bind (fun boolean => ?_)
        dsimp only [tail]
        cases boolean <;> first
          | exact MonoM.refl _
          | exact ((monoAll n k bound).expr cfg env b).bind (fun _ => MonoM.refl _)
    exact composition.of_source (fun n => ⟨n + 1,by simp only [Bool.false_eq_true,ite_false,ite_true,evalExpr,tail]⟩)

theorem typedExprReflection_and {fuel : Nat} {cfg : Cfg} {results : List Ty} {a b : Expr}
    (left : TypedExprReflection fuel cfg results a)
    (right : ∀ residual, residual ≤ fuel → TypedExprReflection residual cfg results b) :
    TypedExprReflection fuel cfg results (.and a b) := typedExprReflection_shortCircuit left right true

theorem typedExprReflection_or {fuel : Nat} {cfg : Cfg} {results : List Ty} {a b : Expr}
    (left : TypedExprReflection fuel cfg results a)
    (right : ∀ residual, residual ≤ fuel → TypedExprReflection residual cfg results b) :
    TypedExprReflection fuel cfg results (.or a b) := typedExprReflection_shortCircuit left right false

end Goose.Lower

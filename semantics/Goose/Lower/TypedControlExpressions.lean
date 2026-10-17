import Goose.Lower.TypedBlocks

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

private theorem expressionBlockSource {cfg : Cfg} {env : Env} {expr : Expr} {initial state : St}
    (root : ExprSource cfg env expr initial) {path : List Nat} {block : Core.Block}
    (context : EvaluationContext cfg.mod root.plans path (.block block) .block)
    (tn tn' : Nat) (ty : Ty) (rst rst' : RState) (roots : List RootRef) (range : Nat × Nat)
    (active : context.ActiveMatches (exprEnv root.typingEnv))
    (access : context.AccessMatches root.typingEnv root.rootsEnv)
    (protection : ShrinkProtected root.world.D root.world.A
      (context.mayShrink root.world.ownerP root.observation))
    (observed : ObservedSafe cfg.mod root.world
      (context.mayShrink root.world.ownerP root.observation) root.observation state.store)
    (classified : cfg.mod.profile = .shrink →
      ClassifiedParameters cfg.mod root.world.P root.world.D root.observation state.store)
    (frame : Core.Sound.Frame cfg.mod root.world root.typingEnv root.rootsEnv env state context.inputFuture)
    (typed : tyBlock (exprEnv root.typingEnv) [] block tn = .ok (ty, tn'))
    (rooted : rpBlockValue root.rootsEnv [] block rst = .ok ((roots, range), rst'))
    (effects : EffLe rst'.eff root.world.E) :
    ∃ source : BlockSource cfg env [] block state,
      source.typingEnv = exprEnv root.typingEnv ∧ source.rootsEnv = root.rootsEnv := by
  cases block with
  | mk scope stmts value =>
    obtain ⟨fresh, inner, tn1, after, tn2, declare, hstmts, hvalue⟩ :=
      tyBlock_ok _ _ _ _ _ _ _ _ typed
    obtain ⟨same, visible, _, _⟩ := declarePre_ok _ _ _ _ _ _ declare
    obtain ⟨_, middle, rstmts, rvalue, escape, _⟩ :=
      rpBlockValue_ok _ _ _ _ _ _ _ _ _ rooted
    have declaration : ({ exprEnv root.typingEnv with scopes := scope :: (exprEnv root.typingEnv).scopes }, tn) =
        (inner, tn1) := by
      simp only [declarePre] at declare
      exact ((st_pure_ok _ _ _).1 declare).symm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj declaration
    have innerActive : context.ActiveMatches { exprEnv root.typingEnv with
        scopes := scope :: (exprEnv root.typingEnv).scopes } := by
      cases context <;> exact active
    have stateEq : { rst with nextVar := rst.nextVar + ([] : List VarId).length } = rst := by
      cases rst
      rfl
    rw [stateEq] at rstmts
    exact ⟨{
      accepted := root.accepted, plans := root.plans, path := path, context := context,
      observation := root.observation, world := root.world,
      typingEnv := exprEnv root.typingEnv, typingInner := _, typingAfter := after,
      rootsEnv := root.rootsEnv, typingStart := tn, typingValue := tn2, typingEnd := tn',
      ty := ty, rootsStart := rst, rootsValue := middle, rootsEnd := rst', roots := roots,
      lowerBound := rst.nextVar, active := innerActive,
      access := by simpa [exprEnv, EvaluationContext.AccessMatches, NodeContext.AccessMatches] using access,
      protection := protection, observed := observed, classified := classified,
      permission := root.permission,
      frame := frame.tenv_congr rfl rfl rfl (fun _ h => h), fresh := fresh, same := same,
      visible := by intro x; simpa using visible x,
      pretyped := ⟨List.nodup_nil, fun _ _ h => by cases h⟩,
      bounded := Nat.le_refl _, typed := hstmts,
      typedValue := by
        cases value with
        | none => exact hvalue.1
        | some expr => exact hvalue,
      rooted := by simpa [Core.Block.scope, Core.Block.stmts] using rstmts, rootedValue := by cases value <;> exact rvalue,
      effects := effects, rootsEscape := escape }, rfl, rfl⟩

theorem ExprSource.blockEChild {cfg : Cfg} {env : Env} {state : St} {block : Core.Block}
    (root : ExprSource cfg env (.blockE block) state) :
    ∃ source : BlockSource cfg env [] block state,
      source.typingEnv = exprEnv root.typingEnv ∧ source.rootsEnv = root.rootsEnv := by
  have typed := root.typed
  simp only [tyExpr] at typed
  have rooted := root.rooted
  simp only [rpExpr] at rooted
  inv at rooted
  obtain ⟨roots, low, high, middle, hblock, hroots, hend⟩ := rooted
  cases hroots
  cases hend
  let ec := root.context
  let child := ec.child rfl 0 (.block block) .block rfl (by trivial)
  have active := ec.child_activeMatches rfl 0 (.block block) .block rfl (by trivial)
    root.typingEnv (exprEnv root.typingEnv) root.active (by intro x; rfl)
  have access := (ec.child_accessMatches_iff rfl 0 (.block block) .block rfl (by trivial)
    root.typingEnv root.rootsEnv).mpr root.access
  have shrinkEq : child.mayShrink root.world.ownerP root.observation =
      ec.mayShrink root.world.ownerP root.observation := by
    funext r
    exact propext (ec.child_mayShrink_iff rfl 0 (.block block) .block rfl (by trivial)
      root.world.ownerP root.observation r)
  have childOutput : child.outputFuture = ec.outputFuture := by
    dsimp only [child]
    cases ec with
    | pilot profile active => rfl
    | shrink profile context =>
      let transition := context.child rfl 0 (.block block) .block rfl (by trivial)
      change transition.context.expected.frame.future = context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      exact DemandNode.childFrame_future transition.childFrameEq rfl
  have childInput : child.inputFuture = ec.inputFuture := by
    have formula : child.inputFuture = block.variables ++ child.outputFuture := by
      dsimp only [child]
      cases ec <;> rfl
    rw [formula, childOutput]
    cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
      NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
      Block.variables, Expr.variables, DemandNode.visibleAfter, List.append_assoc]
  exact expressionBlockSource root child root.typingStart root.typingEnd root.ty root.rootsStart
    root.rootsEnd root.roots (low, high) active access (by simpa [shrinkEq] using root.protection)
    (by simpa [shrinkEq] using root.observed) root.classified
    (by simpa [childInput] using root.frame) typed hblock root.effects

theorem ExprSource.ifEChildren {cfg : Cfg} {env : Env} {state : St}
    {cond : Expr} {thenBlock elseBlock : Core.Block}
    (root : ExprSource cfg env (.ifE cond thenBlock elseBlock) state) (n : Nat) :
    ∃ condition : ExprSource cfg env cond state,
      condition.typingEnv = root.typingEnv ∧ condition.rootsEnv = root.rootsEnv ∧
      condition.ty = .bool ∧ ∀ branch after,
      evalExpr n cfg env cond state = .ok (.bool branch) after →
      ∃ body : BlockSource cfg env [] (if branch then thenBlock else elseBlock) after,
        body.typingEnv = exprEnv root.typingEnv ∧ body.rootsEnv = root.rootsEnv := by
  have typed := root.typed
  simp only [tyExpr] at typed
  inv at typed
  obtain ⟨tc, t1, htc, rfl, tt, t2, htt, ft, t3, htf, heq, hty, hend⟩ := typed
  cases hty
  cases hend
  have hft : ft = root.ty := by
    have h : root.ty = ft := by simpa using heq
    exact h.symm
  cases hft
  have rooted := root.rooted
  simp only [rpExpr] at rooted
  inv at rooted
  obtain ⟨rc, r1, hrc, rt, lt1, lt2, r2, hrt, rf, lf1, lf2, r3, hrf, hroots, hend⟩ := rooted
  cases hend
  let ec := root.context
  let cc := ec.child rfl 0 (.expression cond) .expression rfl (by trivial)
  have condShrink : cc.mayShrink root.world.ownerP root.observation =
      ec.mayShrink root.world.ownerP root.observation := by
    funext r
    exact propext (ec.child_mayShrink_iff rfl 0 (.expression cond) .expression rfl (by trivial)
      root.world.ownerP root.observation r)
  have condOutput : cc.outputFuture =
      match (generalizing := false) ec with
      | .pilot _ active => active
      | .shrink _ context => thenBlock.variables ++ elseBlock.variables ++ context.expected.frame.future := by
    dsimp only [cc]
    cases ec with
    | pilot profile active => rfl
    | shrink profile context =>
      let transition := context.child rfl 0 (.expression cond) .expression rfl (by trivial)
      change transition.context.expected.frame.future =
        thenBlock.variables ++ elseBlock.variables ++ context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      exact DemandNode.childFrame_future transition.childFrameEq rfl
  have condFrame : Core.Sound.Frame cfg.mod root.world root.typingEnv root.rootsEnv env state cc.inputFuture := by
    have parentFrame := root.frame
    change Core.Sound.Frame cfg.mod root.world root.typingEnv root.rootsEnv env state ec.inputFuture at parentFrame
    have formula : cc.inputFuture = cond.variables ++ cc.outputFuture := by
      dsimp only [cc]
      cases ec <;> rfl
    rw [formula, condOutput]
    cases hec : ec with
    | pilot profile active =>
      apply parentFrame.narrowFuture
      intro x hx
      simp only [hec, EvaluationContext.inputFuture, DemandNode.variables, Expr.variables,
        List.mem_append] at hx ⊢
      rcases hx with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr h
    | shrink profile context =>
      simpa [hec, EvaluationContext.inputFuture, NodeContext.inputFuture,
        DemandNode.variables, Expr.variables, List.append_assoc] using parentFrame
  let condition : ExprSource cfg env cond state := {
    accepted := root.accepted, plans := root.plans, path := root.path ++ [0], context := cc,
    observation := root.observation, world := root.world, typingEnv := root.typingEnv,
    rootsEnv := root.rootsEnv, typingStart := root.typingStart, typingEnd := t1,
    ty := .bool, rootsStart := root.rootsStart, rootsEnd := r1, roots := rc,
    active := ec.child_activeMatches rfl 0 (.expression cond) .expression rfl (by trivial)
      root.typingEnv root.typingEnv root.active (by intro x; rfl),
    access := (ec.child_accessMatches_iff rfl 0 (.expression cond) .expression rfl (by trivial)
      root.typingEnv root.rootsEnv).mpr root.access,
    protection := by simpa [condShrink] using root.protection,
    observed := by simpa [condShrink] using root.observed,
    classified := root.classified, permission := root.permission,
    frame := condFrame, typed := htc, rooted := hrc,
    effects := (rpBlockValue_mono hrt).2.trans ((rpBlockValue_mono hrf).2.trans root.effects) }
  refine ⟨condition, rfl, rfl, rfl, ?_⟩
  intro branch after hdone
  have result := condition.result n (.bool branch) hdone
  let block := if branch then thenBlock else elseBlock
  let index := if branch then 1 else 2
  have hchild : (DemandNode.expression (.ifE cond thenBlock elseBlock)).child? index =
      some (.block block) := by cases branch <;> rfl
  let bc := ec.child rfl index (.block block) .block hchild (by trivial)
  have active := ec.child_activeMatches rfl index (.block block) .block hchild (by trivial)
    root.typingEnv (exprEnv root.typingEnv) root.active (by intro x; rfl)
  have access := (ec.child_accessMatches_iff rfl index (.block block) .block hchild (by trivial)
    root.typingEnv root.rootsEnv).mpr root.access
  have bodyShrink : bc.mayShrink root.world.ownerP root.observation =
      ec.mayShrink root.world.ownerP root.observation := by
    funext r
    exact propext (ec.child_mayShrink_iff rfl index (.block block) .block hchild (by trivial)
      root.world.ownerP root.observation r)
  have bodyOutput : bc.outputFuture = ec.outputFuture := by
    dsimp only [bc]
    cases ec with
    | pilot profile active => cases branch <;> rfl
    | shrink profile context =>
      let transition := context.child rfl index (.block block) .block hchild (by trivial)
      change transition.context.expected.frame.future = context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      simp only [DemandNode.phaseFuture]
      exact DemandNode.childFrame_future
        (expectation := ⟨context.expected.frame.active, context.expected.frame.future⟩)
        transition.childFrameEq (by cases branch <;> rfl)
  have bodyInput : bc.inputFuture = block.variables ++ bc.outputFuture := by
    dsimp only [bc]
    cases ec <;> rfl
  have bodyFrame : Core.Sound.Frame cfg.mod root.world root.typingEnv root.rootsEnv env after
      bc.inputFuture := by
    apply result.frame.changeFuture
    intro x hx needed
    change x ∈ cc.outputFuture
    rw [bodyInput, bodyOutput] at needed
    rw [condOutput]
    cases hec : ec with
    | pilot profile live =>
      have hactive := root.active
      change ec.ActiveMatches root.typingEnv at hactive
      rw [hec] at hactive
      exact (hactive x).mpr hx
    | shrink profile context =>
      rw [hec] at needed
      simp only [EvaluationContext.outputFuture, NodeContext.outputFuture] at needed
      cases branch <;>
        simp only [block, Bool.false_eq_true, ↓reduceIte, List.mem_append] at needed ⊢
      · rcases needed with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · rcases needed with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
  have bodyTyped : tyBlock (exprEnv root.typingEnv) [] block (if branch then t1 else t2) =
      .ok (root.ty, if branch then t2 else root.typingEnd) := by
    cases branch <;> simp only [block, Bool.false_eq_true, ↓reduceIte]
    · exact htf
    · exact htt
  have bodyRooted : rpBlockValue root.rootsEnv [] block (if branch then r1 else r2) =
      .ok ((if branch then rt else rf, if branch then (lt1, lt2) else (lf1, lf2)),
        if branch then r2 else root.rootsEnd) := by
    cases branch <;> simp only [block, Bool.false_eq_true, ↓reduceIte]
    · exact hrf
    · exact hrt
  exact expressionBlockSource root bc _ _ _ _ _ _ _ active access
    (by simpa [bodyShrink] using root.protection)
    (by simpa [condition, bodyShrink, condShrink] using result.observed)
    result.classified bodyFrame bodyTyped bodyRooted (by
      cases branch <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact root.effects
      · exact (rpBlockValue_mono hrf).2.trans root.effects)

theorem BlockSource.expressionFlow {cfg : Cfg} {env : Env} {state after : St} {block : Core.Block}
    (source : BlockSource cfg env [] block state) (n : Nat) (flow : Flow)
    (loops : source.typingEnv.loops = 0) (inExpr : source.typingEnv.inExpr = true)
    (done : execBlock n cfg env [] block state = .ok flow after) :
    ∃ value, flow = .normal value := by
  have result := source.result n flow done
  cases flow with
  | normal value => exact ⟨value, rfl⟩
  | brk => exact False.elim (result.flow.1 loops)
  | cont => exact False.elim (result.flow loops)
  | ret value => have h := result.flow.1; rw [inExpr] at h; cases h

def TypedBlockValueClaim (n : Nat) (cfg : Cfg) (results : List Ty) (block : Core.Block) : Prop :=
  ∀ (env : Env) (state : St) (source : BlockSource cfg env [] block state),
    SourceResults source.typingEnv source.rootsEnv results → source.typingEnv.loops = 0 →
    source.typingEnv.inExpr = true →
    ∀ (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerBlock none [] true block (lowerEnv cfg.mod env.vars results) ls = (r, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    SimEAt cx pt fr (blockValue n cfg env block)
      (fun value pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r, .val value)]) state

theorem typedBlockValueClaim_zero (cfg : Cfg) (results : List Ty) (block : Core.Block) :
    TypedBlockValueClaim 0 cfg results block := by
  intro env state source metadata loops inExpr ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  simp only [blockValue]
  exact SimEAt.of_timeout state

theorem typedBlockValueClaim_succ {n : Nat} {cfg : Cfg} {results : List Ty} {block : Core.Block}
    (body : TypedBlockLoopSimulation n cfg results none [] [] true block) :
    TypedBlockValueClaim (n + 1) cfg results block := by
  intro env state source metadata loops inExpr ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  have hs := body.function env state source metadata loops ls ls' r pt cx fr hlow hpp hext hrel
    trivial hgir hresults hgenerated
  have prepareEq : (execBlock n cfg env [] block >>= prepareReturn env) state =
      execBlock n cfg env [] block state := by
    rw [bind_apply]
    cases done : execBlock n cfg env [] block state with
    | stop err final => rfl
    | ok flow after =>
      obtain ⟨value, rfl⟩ := source.expressionFlow n flow loops inExpr done
      rfl
  have hraw : SimEAt cx pt fr (execBlock n cfg env [] block)
      (BlockFlowPost cfg env cx ls fr ls' block true r) state := by
    unfold SimEAt at hs ⊢
    rw [prepareEq] at hs
    exact hs
  simp only [blockValue]
  refine SimEAt.bind hraw fun flow after pt' fr' done post => ?_
  obtain ⟨value, rfl⟩ := source.expressionFlow n flow loops inExpr done
  rcases post with ⟨normal, same, _, P⟩ | ⟨returned, origin, same, site⟩
  · cases same
    exact SimEAt.ret (by simpa [blockCells] using P)
  · cases same

theorem typedExprClaim_blockE {n : Nat} {cfg : Cfg} {results : List Ty} {block : Core.Block}
    (body : TypedBlockValueClaim n cfg results block) :
    TypedExprClaim (n + 1) cfg results (.blockE block) := by
  intro env state source metadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨child, htyping, hroots⟩ := source.blockEChild
  have hmetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    simpa [SourceResults, exprEnv] using metadata
  simp only [lowerExpr] at hlow
  simp only [evalExpr]
  exact body env state child hmetadata (by simp [htyping, exprEnv])
    (by simp [htyping, exprEnv]) ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated

theorem typedExprClaim_ifE {n : Nat} {cfg : Cfg} {results : List Ty} {cond : Expr}
    {thenBlock elseBlock : Core.Block} (conditionClaim : TypedExprClaim n cfg results cond)
    (thenClaim : TypedBlockValueClaim n cfg results thenBlock)
    (elseClaim : TypedBlockValueClaim n cfg results elseBlock) :
    TypedExprClaim (n + 1) cfg results (.ifE cond thenBlock elseBlock) := by
  intro env state source metadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults hgenerated
  obtain ⟨condition, conditionTyping, conditionRoots, conditionType, next⟩ := source.ifEChildren n
  have conditionMetadata : SourceResults condition.typingEnv condition.rootsEnv results := by
    rw [conditionTyping, conditionRoots]
    exact metadata
  let le := lowerEnv cfg.mod env.vars results
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨cv, ls1, h1, hw⟩ := hlow
  have hadv_w : ls1.Adv ls' :=
    advB_ifE_core cv (sourceBlockScope thenBlock)
      (advB_lowerBlock none [] true thenBlock) (advB_lowerBlock none [] true elseBlock) _ _ _ _ hw
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv hadv_w
  simp only [evalExpr]
  refine SimEAt.bind (conditionClaim env state condition conditionMetadata ls ls1 cv pt cx fr
    h1 hpp hext1 hrel hgir hresults hgenerated) fun va afterCondition pt1 fr1 hdone P1 => ?_
  refine SimEAt.expectBool fun β hva => ?_
  subst hva
  obtain ⟨body, bodyTyping, bodyRoots⟩ := next β afterCondition hdone
  have bodyMetadata : SourceResults body.typingEnv body.rootsEnv results := by
    rw [bodyTyping, bodyRoots]
    simpa [SourceResults, exprEnv] using metadata
  have bodyLoops : body.typingEnv.loops = 0 := by simp [bodyTyping, exprEnv]
  have bodyInExpr : body.typingEnv.inExpr = true := by simp [bodyTyping, exprEnv]
  have hcv : fr1.vals[cv]? = some (.val (.bool β)) := P1.has (cv, _) (by simp)
  obtain ⟨blk1, hc1, hb1, hp1⟩ := LS.pp_some P1.pp
  rw [whenLive_some _ _ _ hc1] at hw
  simp only [bind_eq] at hw
  obtain ⟨⟨tb, eb⟩, lsf, hf, u2, ls2, hs1, vt, ls3, ha1, endT, ls4, hc4, u5, ls5, hs2, vf, ls6, ha2,
    endF, ls7, hc7, joined, ls8, hj, u8, ls9, hrecipe, hp⟩ := hw
  obtain ⟨e4c, e4⟩ := curBlock_eq hc4
  subst e4
  obtain ⟨e7c, e7⟩ := curBlock_eq hc7
  subst e7
  rw [pure_run] at hp
  have hfinal : ls9 = ls' := (Prod.mk.inj hp).2
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
  have hext6 : ExtT ls7 cx.fn.blocks := joinOutputExt.of_ext (joinValue_ext hj)
  have hadv1 := advB_lowerBlock none [] true thenBlock _ _ _ _ ha1
  have hadv2 := advB_lowerBlock none [] true elseBlock _ _ _ _ ha2
  obtain ⟨htb, heb, hinst, ⟨Ttb, hTtb, hTtbp⟩, ⟨Teb, hTeb, hTebp⟩, hpp2, hpp5, hst2, hv2, hst3, hst6,
    hv16, hv36, hendT, hendF, hkeep, hsz36, hsz6⟩ :=
    branch_facts hf hs1 hadv1 hs2 hadv2 P1.pp hext6
  have generatedF := (hgenerated.lowerExpr cond h1).fork cv hf
  obtain ⟨forkIds, forkSize⟩ := fork_ids hf
  have thenBound : tb < lsf.blocks.size := by
    have id : tb = ls1.blocks.size := congrArg Prod.fst forkIds
    rw [id, forkSize]
    nat_omega
  have elseBound : eb < lsf.blocks.size := by
    have id : eb = ls1.blocks.size + 1 := congrArg Prod.snd forkIds
    rw [id, forkSize]
    nat_omega
  have generated2 := generatedF.setCur (some tb)
    (by intro current same; cases same; exact thenBound) hs1
  have generated4 := generated2.lowerBlock none [] true thenBlock trivial ha1
  have elseBound4 : eb < ls4.blocks.size :=
    Nat.lt_of_lt_of_le (by rw [setCur_blocks hs1]; exact elseBound) hadv1.ext.1
  have generated5 := generated4.setCur (some eb)
    (by intro current same; cases same; exact elseBound4) hs2
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
  cases β
  ·
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine SimEAt.goes (goes_condbr_else0 hinst' hcv hTeb hTebp rfl) ?_
    have hrel5 : Rel cfg env cx fr1 ls5 := P1.rel.stack_eq (by rw [e5]; exact hst3)
    refine SimEAt.mono_goes (elseClaim env afterCondition body bodyMetadata bodyLoops bodyInExpr
      ls5 ls7 vf (eb, 0) cx fr1 ha2 hpp5 hext6 hrel5 hgir hresults generated5) ?_
    intro v finalState pt7 fr7 blockDone P7
    obtain ⟨blk7, hc7', hb7, hp7⟩ := LS.pp_some P7.pp
    have hendF' : endF = some pt7.1 := by rw [e7c]; exact hc7'
    have hlive : endT.isSome ∨ endF.isSome := Or.inr (by rw [hendF']; rfl)
    obtain ⟨ty, hr, hvj, hstj, hbj, hcj, hTj, hFj⟩ := joinValue_facts hj joinOutputExt hlive hnd hltT hltF
    have hresult : r = ls7.vals.size := (Prod.mk.inj hp).1.symm.trans hr
    have finalPp : ls'.pp = some (ls7.blocks.size, 0) := by
      rw [← hfinal, ← recipePp]
      exact LS.pp_eq hcj hbj
    have hinstF := hFj pt7.1 blk7 hendF' hb7
    obtain ⟨Tjb, hTjb, hTjbp⟩ := joinOutputExt.params hbj
    have hcell : fr7.vals[vf]? = some (.val v) := P7.has (vf, _) (by simp)
    have hpt7 : pt7 = (pt7.1, blk7.insts.size) := Prod.ext rfl hp7
    have hi7 : instAt cx.fn pt7 = some (.term (.br ls7.blocks.size [vf])) := by
      rw [hpt7]; exact hinstF
    have g2 := goes_br1 hi7 hTjb hTjbp hcell
    refine ⟨(ls7.blocks.size, 0), fr7.set ls7.vals.size (.val v), g2, ?_⟩
    rw [hresult]
    have hsame : Same ls.vals.size fr fr7 := by
      refine P1.same.trans (P7.same.mono ?_) P1.mono
      rw [e5]; show ls1.vals.size ≤ ls4.vals.size; exact hmono_all
    exact Post.join hsame (P7.rel.stack_eq (hrel.stack.trans P7.rel.stack.symm)) (by nat_omega)
      (by rw [finalVals]; nat_omega) (by rw [finalVals]; nat_omega)
      (finalStack.trans (hstj.trans hst_out)) finalPp
  ·
    simp only [↓reduceIte]
    refine SimEAt.goes (goes_condbr_then0 hinst' hcv hTtb hTtbp rfl) ?_
    refine SimEAt.mono_goes (thenClaim env afterCondition body bodyMetadata bodyLoops bodyInExpr
      ls2 ls4 vt (tb, 0) cx fr1 ha1 hpp2' hext4 hrel2 hgir hresults generated2) ?_
    intro v finalState pt3 fr3 blockDone P3
    obtain ⟨blk3, hc3, hb3, hp3⟩ := LS.pp_some P3.pp
    have hendT' : endT = some pt3.1 := by rw [e4c]; exact hc3
    have hlive : endT.isSome ∨ endF.isSome := Or.inl (by rw [hendT']; rfl)
    obtain ⟨ty, hr, hvj, hstj, hbj, hcj, hTj, hFj⟩ := joinValue_facts hj joinOutputExt hlive hnd hltT hltF
    have hresult : r = ls7.vals.size := (Prod.mk.inj hp).1.symm.trans hr
    have finalPp : ls'.pp = some (ls7.blocks.size, 0) := by
      rw [← hfinal, ← recipePp]
      exact LS.pp_eq hcj hbj
    have hne : pt3.1 ≠ eb := (hendT pt3.1 hc3).2.1
    have hb7 : ls7.blocks[pt3.1]? = some blk3 := hkeep pt3.1 blk3 hb3 hne
    have hinstT := hTj pt3.1 blk3 hendT' hb7
    obtain ⟨Tjb, hTjb, hTjbp⟩ := joinOutputExt.params hbj
    have hcell : fr3.vals[vt]? = some (.val v) := P3.has (vt, _) (by simp)
    have hpt3 : pt3 = (pt3.1, blk3.insts.size) := Prod.ext rfl hp3
    have hi3 : instAt cx.fn pt3 = some (.term (.br ls7.blocks.size [vt])) := by
      rw [hpt3]; exact hinstT
    have g2 := goes_br1 hi3 hTjb hTjbp hcell
    refine ⟨(ls7.blocks.size, 0), fr3.set ls7.vals.size (.val v), g2, ?_⟩
    rw [hresult]
    have hsame : Same ls.vals.size fr fr3 := by
      refine P1.same.trans (P3.same.mono ?_) P1.mono
      nat_omega
    exact Post.join hsame (P3.rel.stack_eq (hrel.stack.trans P3.rel.stack.symm)) (by nat_omega)
      (by rw [finalVals]; nat_omega) (by rw [finalVals]; nat_omega)
      (finalStack.trans (hstj.trans hst_out)) finalPp


end Goose.Lower

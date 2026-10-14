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
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results →
    SimEAt cx pt fr (blockValue n cfg env block)
      (fun value pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r, .val value)]) state

theorem typedBlockValueClaim_zero (cfg : Cfg) (results : List Ty) (block : Core.Block) :
    TypedBlockValueClaim 0 cfg results block := by
  intro env state source metadata loops inExpr ls ls' r pt cx fr hlow hpp hext hrel hgir hresults
  simp only [blockValue]
  exact SimEAt.of_timeout state

theorem typedBlockValueClaim_succ {n : Nat} {cfg : Cfg} {results : List Ty} {block : Core.Block}
    (body : TypedBlockLoopSimulation n cfg results none [] [] true block) :
    TypedBlockValueClaim (n + 1) cfg results block := by
  intro env state source metadata loops inExpr ls ls' r pt cx fr hlow hpp hext hrel hgir hresults
  have hs := body.function env state source metadata loops ls ls' r pt cx fr hlow hpp hext hrel
    trivial hgir hresults
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
  intro env state source metadata ls ls' r pt cx fr hlow hpp hext hrel hgir hresults
  obtain ⟨child, htyping, hroots⟩ := source.blockEChild
  have hmetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [htyping, hroots]
    simpa [SourceResults, exprEnv] using metadata
  simp only [lowerExpr] at hlow
  simp only [evalExpr]
  exact body env state child hmetadata (by simp [htyping, exprEnv])
    (by simp [htyping, exprEnv]) ls ls' r pt cx fr hlow hpp hext hrel hgir hresults

end Goose.Lower

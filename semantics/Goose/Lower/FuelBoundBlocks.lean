import Goose.Lower.FuelBoundEndpoints
import Goose.Lower.FuelBoundControlSteps
import Goose.Lower.ReflectionControl
import Goose.Lower.ReflectionBlocksScope
import Goose.Lower.TypedControlExpressions

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

private theorem constantFuelBound {sourceFuel targetFuel : Nat} {cx : FnCtx} {pt : Pt} {fr : Frame}
    {action : M α} {post : α → St → Pt → Frame → Prop} {state : St}
    (reflection : ReflectAtFuel targetFuel cx pt fr (fun _ => action) post state) :
    FuelBoundAt sourceFuel targetFuel cx pt fr (fun _ => action) post state := by
  intro result final run
  rcases reflection result final run with success | stopped
  · obtain ⟨_, value, after, pt', fr', residual, sourceRun, matched, bound, continuation⟩ := success
    exact Or.inl ⟨value, after, pt', fr', residual, sourceRun, matched, bound, continuation⟩
  · obtain ⟨_, stop, after, sourceRun, resultEq⟩ := stopped
    exact Or.inr ⟨stop, after, sourceRun, resultEq⟩

theorem block_enter_fuelBoundAt {sourceFuel fuel : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls ls1 : LS} {fr : Frame} {pt : Pt} {le : LEnv} {scope : ScopeId} (state : St)
    (point : ls.pp = some pt) (run : emitEffect (.enter scope) le ls = ((), ls1))
    (extension : ExtT ls1 cx.fn.blocks) (rel : Rel cfg env cx fr ls) :
    FuelBoundAt sourceFuel fuel cx pt fr (fun _ => freshScope)
      (fun scopeInstance _ pt' fr' =>
        ls1.pp = some pt' ∧ ls1.vals.size = ls.vals.size ∧ fr'.vals = fr.vals ∧
        Rel cfg { env with scopes := (scope, scopeInstance) :: env.scopes } cx fr'
          { ls1 with stack := scope :: ls1.stack }) state := by
  exact constantFuelBound (block_enter_reflectAtFuel fuel state point run extension rel)

theorem block_leave_fuelBoundAt {sourceFuel fuel : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {lsk lsLeave : LS} {fr : Frame} {pt : Pt} {le : LEnv} {scope : ScopeId} {scopeInstance : ScopeInst}
    (state : St) (point : lsk.pp = some pt) (run : emitEffect (.leave scope) le lsk = ((), lsLeave))
    (extension : ExtT lsLeave cx.fn.blocks)
    (rel : Rel cfg { env with scopes := (scope, scopeInstance) :: env.scopes } cx fr lsk) :
    FuelBoundAt sourceFuel fuel cx pt fr (fun _ => Core.releaseScope env scope scopeInstance)
      (fun _ _ pt' fr' => lsLeave.pp = some pt' ∧ lsLeave.vals.size = lsk.vals.size ∧
        fr'.vals = fr.vals ∧ Rel cfg env cx fr' { lsLeave with stack := lsLeave.stack.drop 1 }) state := by
  exact constantFuelBound (block_leave_reflectAtFuel fuel state point run extension rel)

theorem initSlots_fuelBoundAt {sourceFuel fuel : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {scope : ScopeId} {scopeInstance : ScopeInst} (headScope : env.scopes.head? = some (scope, scopeInstance))
    (pre : List (SlotId × ValueId × OriginId)) (pre' : List (VarId × Val)) {le : LEnv}
    {before after : LS} {unitValue : Unit} {point : Pt} {frame : Frame} (state : St)
    (members : ∀ item ∈ pre, ∃ localVar, env.vars[item.1]? = some localVar ∧ localVar.scope = scope)
    (lowering : initSlots pre le before = (unitValue, after)) (pointEq : before.pp = some point)
    (extension : ExtT after cx.fn.blocks) (rel : Rel cfg env cx frame before)
    (preRel : PreRel frame pre pre') :
    FuelBoundAt sourceFuel fuel cx point frame (fun _ => bindAll env.act scopeInstance pre')
      (fun _ _ point' frame' => after.pp = some point' ∧ frame' = frame ∧
        after.stack = before.stack ∧ after.vals = before.vals) state := by
  exact constantFuelBound (initSlots_reflectAtFuel headScope pre pre' (le := le) (lsk := before)
    (ls_i := after) (u := unitValue) (ptk := point) (frk := frame) (fuel := fuel)
    state members lowering pointEq extension rel preRel)

theorem typedStatementsFuelBound_nil {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx}
    (positive : 0 < sourceFuel) :
    TypedStatementsFuelBound sourceFuel fuel cfg results loop [] := by
  intro env state source metadata loops ls after pt cx fr lowering point extension rel moduleEq
    resultsEq depth targets counter generated frames
  simp only [lowerStmts, pure_run] at lowering
  obtain ⟨_, rfl⟩ := Prod.mk.inj lowering
  cases sourceFuel with
  | zero => omega
  | succ sourceFuel =>
    have reflected : FuelBoundAt (sourceFuel + 1) fuel cx pt fr (fun _ => pure (Flow.normal .unit))
        (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr ls loop flow pt' fr') state := by
      exact FuelBoundAt.ret (Or.inl ⟨rfl, Post.init rel point⟩)
    apply reflected.of_source
    cases loop <;> simp [execStmts, prepareLoopFlow, prepareReturn, prepareLoopExit]

theorem typedStatementsFuelBound_cons {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {statement : Stmt} {rest : List Stmt}
    (head : TypedStatementFuelBound sourceFuel fuel cfg results loop statement)
    (tail : ∀ residual, residual ≤ fuel → TypedStatementsFuelBound sourceFuel residual cfg results loop rest) :
    TypedStatementsFuelBound (sourceFuel + 1) fuel cfg results loop (statement :: rest) := by
  intro env state source metadata loops ls after pt cx fr lowering point extension rel moduleEq
    resultsEq depth targets counter generated frames
  obtain ⟨block, live, _, _⟩ := LS.pp_some point
  simp only [lowerStmts, bind_eq] at lowering
  obtain ⟨isLive, initial, test, lowering⟩ := lowering
  rw [isLive_run live] at test
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj test
  simp only [ite_true, bind_eq] at lowering
  obtain ⟨ignored, middle, headRun, tailRun⟩ := lowering
  cases ignored
  have middleExtension := extension.of_adv (advB_lowerStmts loop rest _ _ _ _ tailRun)
  obtain ⟨headSource, typing, roots, nextSource⟩ := source.split
  have headMetadata : SourceResults headSource.typingEnv headSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  have headLoops : LoopSourceMatches headSource.typingEnv loop := by rw [typing]; exact loops
  have first := head env state headSource headMetadata headLoops ls middle pt cx fr headRun point
    middleExtension rel moduleEq resultsEq depth targets counter generated frames
  have middleGenerated := generated.lowerStmt loop statement frames.toTargets headRun
  have middleFrames := frames.mono (advB_lowerStmt loop statement _ _ _ _ headRun).ext
  have composed : FuelBoundAt sourceFuel fuel cx pt fr
      (fun n => (execStmt n cfg env statement >>= prepareLoopFlow env loop) >>= loopStmtsTail n cfg env loop rest)
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine first.bind ?_
    intro flow next pt' fr' done matched residual bound
    rcases matched with ⟨rfl, post⟩ | returned | ⟨context, loopEq, transfer⟩
    ·
      have raw := preparedLoopFlow_normal_success done
      obtain ⟨tailSource, tailTyping, tailRoots, _⟩ := nextSource sourceFuel .unit next raw
      have tailMetadata : SourceResults tailSource.typingEnv tailSource.rootsEnv results := by
        apply headMetadata.transport
        · rw [tailTyping]
          exact (headSource.result sourceFuel (.normal .unit) raw).same.impl
        · rw [tailRoots, roots]
      have tailLoops : LoopSourceMatches tailSource.typingEnv loop := by
        apply headLoops.transport
        rw [tailTyping]
        exact (headSource.result sourceFuel (.normal .unit) raw).same.loops
      have tailBound := tail residual bound env next tailSource tailMetadata tailLoops middle after pt' cx fr'
        tailRun post.pp extension post.rel moduleEq resultsEq depth targets (counter.afterPost post)
        middleGenerated middleFrames
      simpa only [loopStmtsTail] using tailBound.mono
        (fun _ _ _ _ matched => StatementLoopPost.prefix rel post counter matched)
    · obtain ⟨value, origin, rfl, site⟩ := returned
      simpa only [loopStmtsTail] using
        (FuelBoundAt.ret (Or.inr (Or.inl ⟨value, origin, rfl, site⟩)) :
          FuelBoundAt sourceFuel residual cx pt' fr' (fun _ => pure (.ret value))
            (fun next _ pt'' fr'' => StatementLoopPost cfg env cx ls fr after loop next pt'' fr'') next)
    · rcases transfer with ⟨rfl, exit⟩ | ⟨rfl, continued⟩
      · simpa only [loopStmtsTail] using
          (FuelBoundAt.ret (Or.inr (Or.inr ⟨context, loopEq, Or.inl ⟨rfl, exit⟩⟩)) :
            FuelBoundAt sourceFuel residual cx pt' fr' (fun _ => pure .brk)
              (fun next _ pt'' fr'' => StatementLoopPost cfg env cx ls fr after loop next pt'' fr'') next)
      · simpa only [loopStmtsTail] using
          (FuelBoundAt.ret (Or.inr (Or.inr ⟨context, loopEq, Or.inr ⟨rfl, continued⟩⟩)) :
            FuelBoundAt sourceFuel residual cx pt' fr' (fun _ => pure .cont)
              (fun next _ pt'' fr'' => StatementLoopPost cfg env cx ls fr after loop next pt'' fr'') next)
  exact composed.of_source
    (congrFun (prepareLoopFlow_execStmts sourceFuel cfg env loop statement rest) state)

theorem TypedBlockFuelBound.value {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {block : Core.Block}
    (reflection : TypedBlockFuelBound sourceFuel fuel cfg results none [] [] true block)
    (env : Env) (state : St) (source : BlockSource cfg env [] block state)
    (metadata : SourceResults source.typingEnv source.rootsEnv results)
    (loops : source.typingEnv.loops = 0) (inExpr : source.typingEnv.inExpr = true)
    (ls after : LS) (result : ValueId) (pt : Pt) (cx : FnCtx) (fr : Frame)
    (lowering : lowerBlock none [] true block (lowerEnv cfg.mod env.vars results) ls = (result, after))
    (point : ls.pp = some pt) (extension : ExtT after cx.fn.blocks) (rel : Rel cfg env cx fr ls)
    (moduleEq : cx.cfg.mod = lower cfg.mod) (resultsEq : cx.fn.results = results)
    (generated : GeneratedBuilderState ls) :
    FuelBoundAt (sourceFuel + 1) fuel cx pt fr (fun n => blockValue n cfg env block)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(result, .val value)]) state := by
  have prepared := reflection.function env state source metadata loops ls after result pt cx fr lowering point
    extension rel trivial moduleEq resultsEq generated
  have preparedEq :
      (execBlock sourceFuel cfg env [] block >>= prepareReturn env) state =
        execBlock sourceFuel cfg env [] block state := by
    rw [bind_apply]
    cases done : execBlock sourceFuel cfg env [] block state with
    | stop stop after => rfl
    | ok flow after =>
      obtain ⟨value, rfl⟩ := source.expressionFlow sourceFuel flow loops inExpr done
      simp only [prepareReturn]
      rfl
  have raw := prepared.of_source (other := fun n => execBlock n cfg env [] block)
    (otherFuel := sourceFuel) preparedEq.symm
  have valueBound : FuelBoundAt sourceFuel fuel cx pt fr
      (fun n => execBlock n cfg env [] block >>= expectNormal)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(result, .val value)]) state := by
    refine raw.bind ?_
    intro flow after' pt' fr' done matched residual bound
    obtain ⟨value, rfl⟩ := source.expressionFlow sourceFuel flow loops inExpr done
    rcases matched with ⟨targetValue, flowEq, unitValue, post⟩ | returned
    · cases flowEq
      exact FuelBoundAt.ret (by
        simpa only [blockCells, Core.Block.value, Core.Block.scope, Bool.or_true, ↓reduceIte] using post)
    · rcases returned with ⟨value, origin, flowEq, site⟩
      cases flowEq
  have blockBound := valueBound.of_source (other := fun n => blockValue n cfg env block)
    (otherFuel := sourceFuel + 1) (by simp only [blockValue])
  simpa only [blockValue] using blockBound

theorem typedExprFuelBound_blockE {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {block : Core.Block}
    (reflection : TypedBlockFuelBound sourceFuel fuel cfg results none [] [] true block) :
    TypedExprFuelBound (sourceFuel + 2) fuel cfg results (.blockE block) := by
  intro env state source metadata ls after result pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨child, typing, roots, _⟩ := source.blockEChild
  have childMetadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [typing, roots]
    simpa [SourceResults, exprEnv] using metadata
  simp only [lowerExpr] at lowering
  have loops : child.typingEnv.loops = 0 := by simp [typing, exprEnv]
  have inExpr : child.typingEnv.inExpr = true := by simp [typing, exprEnv]
  have childValue := reflection.value env state child childMetadata loops inExpr ls after result pt cx fr
    lowering point extension rel moduleEq resultsEq generated
  have indexed := childValue.of_source
    (other := fun n => evalExpr n cfg env (.blockE block)) (otherFuel := sourceFuel + 2) (by
      simp only [evalExpr])
  simpa only [evalExpr] using indexed

end Goose.Lower

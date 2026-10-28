import Goose.Lower.DemandAssignmentScalarAlias

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_assignment_store_step {cfg : Cfg} {env : Env} {place : Place} {expression : Expr}
    {origin : OriginId} {state addressedState valueState after : St}
    (source : StmtSource cfg env (.assign place expression origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    {required map : RetainedSsaMap} {initial frame : GIR.Frame} {initialPoint point : Pt}
    (site : GeneratedAssignmentStoreSite cfg.mod source.rootsEnv.access cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path before loop place expression origin required point)
    (admitted : map.Admitted cfg.mod.profile source.context.retained) (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨initialPoint, initial, state⟩)
    {fuel : Nat} {location : Loc} {value : Val}
    (placed : evalPlace fuel cfg env place state = .ok location addressedState)
    (evaluated : evalExpr fuel cfg env expression addressedState = .ok value valueState)
    (post : Post cfg env cx before initial
      (lowerExpr expression (lowerEnv cfg.mod env.vars results) (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2).2
      frame point [((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location)),
        ((lowerExpr expression (lowerEnv cfg.mod env.vars results) (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2).1, .val value)])
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Evidence.RuntimeStep cx.cfg cx.fn point frame valueState next nextFrame after) :
    next = (point.1, point.2 + 1) ∧ nextFrame = frame ∧
      execStmt (fuel + 1) cfg env (.assign place expression origin) state = .ok (.normal .unit) after ∧
      Post cfg env cx before initial (lowerStmt loop (.assign place expression origin) (lowerEnv cfg.mod env.vars results) before).2
        nextFrame next [] ∧ StmtResult source (.normal .unit) after ∧
      map.Bounded (lowerStmt loop (.assign place expression origin) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      DemandFrameAt cfg env cx source.world source.typingAfter source.rootsEnv source.context.outputFuture
        map.values map.runs ⟨next, nextFrame, after⟩ := by
  let le := lowerEnv cfg.mod env.vars results
  let address := (lowerPlace place le before).1
  let result := (lowerExpr expression le (lowerPlace place le before).2).1
  have addressCell := post.has (address, .val (.ref location)) (by simp [address, le])
  have valueCell := post.has (result, .val value) (by simp [result, le])
  dsimp only [address, result, le] at addressCell valueCell
  cases step with
  | define instruction execution => cases site.instruction.symm.trans instruction
  | effect instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    simp only [execEff, getVal_of addressCell, getVal_of valueCell, expectRef, bind_apply, pure_apply] at execution
    cases write : writeLoc location value valueState with
    | stop reason final => simp [write] at execution
    | ok written final =>
      cases written
      simp only [write, Res.ok.injEq] at execution
      obtain ⟨rfl, rfl⟩ := execution
      have done : execStmt (fuel + 1) cfg env (.assign place expression origin) state = .ok (.normal .unit) final := by
        simp only [execStmt, bind_apply, placed, evaluated, write, pure_apply]
      have emitted : emitEffect (.store address result (some origin)) le
          (lowerExpr expression le (lowerPlace place le before).2).2 =
          ((), (lowerStmt loop (.assign place expression origin) le before).2) := by
        simp only [lowerStmt, bind_run, address, result]
      have finalPost := (Post.eff_leaf post emitted site.extended).1
      have sourceResult := source.result (fuel + 1) (.normal .unit) done
      have retained : RetainsAliases cfg.mod source.world env state.store final.store
          (map.values.map Prod.snd ++ map.runs.map Prod.snd) := by
        cases profile : cfg.mod.profile with
        | pilot => exact retainedAliases_of_storeLe (sourceResult.pilotStore profile) _
        | shrink => exact sourceResult.aliases.subset (admitted profile)
      have carried := realized.retained finalPost.same bounded.1 bounded.2 retained
      exact ⟨rfl, rfl, done, finalPost, sourceResult, bounded.mono finalPost.mono,
        ⟨⟨_, finalPost.pp, finalPost.rel⟩, sourceResult.frame, carried⟩⟩
  | branch instruction read enter => cases site.instruction.symm.trans instruction
  | branchTrue instruction test read enter => cases site.instruction.symm.trans instruction
  | branchFalse instruction test read enter => cases site.instruction.symm.trans instruction

theorem accepted_generated_assignment_store_stop {cfg : Cfg} {env : Env} {place : Place} {expression : Expr}
    {origin : OriginId} {state addressedState valueState after : St}
    (source : StmtSource cfg env (.assign place expression origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    {required : RetainedSsaMap} {initial frame : GIR.Frame} {point : Pt}
    (site : GeneratedAssignmentStoreSite cfg.mod source.rootsEnv.access cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path before loop place expression origin required point)
    {fuel : Nat} {location : Loc} {value : Val}
    (placed : evalPlace fuel cfg env place state = .ok location addressedState)
    (evaluated : evalExpr fuel cfg env expression addressedState = .ok value valueState)
    (post : Post cfg env cx before initial
      (lowerExpr expression (lowerEnv cfg.mod env.vars results) (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2).2
      frame point [((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location)),
        ((lowerExpr expression (lowerEnv cfg.mod env.vars results) (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2).1, .val value)])
    {targetFuel : Nat} {stop : Stop}
    (stopped : DemandInstructionStop cx targetFuel ⟨point, frame, valueState⟩ stop after) (nonTimeout : stop ≠ .timeout) :
    execStmt (fuel + 1) cfg env (.assign place expression origin) state = .stop stop after := by
  have addressCell := post.has ((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location)) (by simp)
  have valueCell := post.has ((lowerExpr expression (lowerEnv cfg.mod env.vars results)
    (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2).1, .val value) (by simp)
  cases stopped with
  | timeout => exact (nonTimeout rfl).elim
  | definition instruction execution => cases site.instruction.symm.trans instruction
  | effect instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    simp only [execEff, getVal_of addressCell, getVal_of valueCell, expectRef, bind_apply, pure_apply] at execution
    cases write : writeLoc location value valueState with
    | ok written final => simp [write] at execution
    | stop reason final =>
      simp only [write, Res.stop.injEq] at execution
      obtain ⟨rfl, rfl⟩ := execution
      simp only [execStmt, bind_apply, placed, evaluated, write]

#print axioms accepted_generated_assignment_store_stop
#print axioms accepted_generated_assignment_store_step

end Goose.Lower

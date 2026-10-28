import Goose.Lower.DemandIfRecursiveElseStopped

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_recursive_if_none_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (depth : Nat) (condition : Expr) (yes : Core.Block) (origin : OriginId)
    (fragment : ∀ state : St, BoundedIfStatements cfg depth
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (branchFamily : RecursiveIfBranchFamily cx results selected depth yes)
    (noValue : yes.value = none)
    (conditionFamily : GeneratedExpressionPrefixFamily cx results selected none condition (@CanonicalExpressionPrefixCursor cfg env cx)) :
    GeneratedStatementPrefixFamily cx results selected none (.ifS condition yes none origin)
      (@RecursiveIfCursor cfg cx results root owner (depth + 1) env selected) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  refine ⟨owned, coverage, ?_⟩
  obtain ⟨child, childType, canonical, progress⟩ := accepted_generated_if_condition_prefix source selected owned occurrence
    rows coverage admitted bounded realized input extended conditionFamily steps
  cases progress with
  | interior demanded => exact .interior (.base (.conditional (.condition child canonical demanded)))
  | @complete fuel consumed remaining current value count executed residual evaluated boundary =>
    have typed := (child.result fuel value evaluated).typed
    rw [childType] at typed
    obtain ⟨boolean, rfl⟩ := hasTy_bool typed
    have lowered : lowerStmt none (.ifS condition yes none origin) (lowerEnv cfg.mod env.vars results) before =
        ((), (lowerStmt none (.ifS condition yes none origin) (lowerEnv cfg.mod env.vars results) before).2) := by
      generalize run : lowerStmt none (.ifS condition yes none origin) (lowerEnv cfg.mod env.vars results) before = output
      cases output with
      | mk returned builder => cases returned; rfl
    obtain ⟨yesBlock, joinBlock, forked, branchStart, branchEnd, jumped, result, forkRun, startEq,
      branchRun, jumpRun, finalEq, forkExtended, branchExtended, jumpExtended, joinPoint, joinStack, joinVals⟩ :=
      generated_if_none_join_builder lowered boundary.post.pp extended
    have cell := boundary.post.has ((lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1, .val (.bool boolean)) (by simp)
    rcases residual.uncons with ⟨_, rfl⟩ | ⟨rest, next, restCount, first, suffix⟩
    · exact .interior (.base (.conditional (.fork child boolean fuel canonical evaluated boundary)))
    · obtain ⟨stepFuel, actual⟩ := runtimeStep_demandInstructionStep first
      have equal := actual.deterministic (generated_if_branch_step (state := current.state) boolean forkRun boundary.post.pp forkExtended cell stepFuel)
      have nextEq : next = ⟨(if boolean then yesBlock else joinBlock, 0), current.frame, current.state⟩ := by
        cases next
        exact equal
      subst next
      cases boolean with
      | false =>
        obtain ⟨actualJoin, branchStep, sourceDone, finalPost⟩ :=
          accepted_generated_if_skip source child canonical evaluated boundary lowered extended
        have joinEq : actualJoin = joinBlock := by
          have same := (branchStep stepFuel).deterministic (generated_if_branch_step (state := current.state) false forkRun boundary.post.pp forkExtended cell stepFuel)
          exact congrArg (fun point : DemandRuntimePoint => point.point.1) same
        subst actualJoin
        apply DemandPrefixDecomposition.complete (sourceFuel := fuel + 1) (value := .normal .unit)
          (consumed := consumed + 1) (remaining := rest) (boundary := ⟨(joinBlock, 0), current.frame, current.state⟩)
        · omega
        · exact executed.append (.next first (.zero _))
        · exact suffix
        · simp [bind_apply, sourceDone, prepareLoopFlow, prepareReturn, pure_apply]
        · exact finalPost
      | true =>
        have branchProgress := accepted_generated_if_generic_then_prefix_canonical source child canonical evaluated selected owned occurrence rows
          coverage admitted input boundary forkRun forkExtended startEq branchRun branchExtended jumpRun jumpExtended
          finalEq joinPoint joinStack joinVals _ (branchFamily current.state branchStart).1
          (fun done => (fragment current.state).recursive.normal done) noValue suffix
        rcases branchProgress with ⟨branch, branchCanonical, demanded⟩ | ⟨branchCount, remaining, final, sourceFuel, branchCountEq, branchExecuted, branchResidual, sourceDone, joinStep, finalPost⟩
        · exact .interior (.branch child true fuel canonical evaluated rfl
          (by simp [DemandNode.child?, DemandNode.children]) branch branchCanonical demanded)
        · rcases branchResidual.uncons with ⟨_, rfl⟩ | ⟨rest', next', restCount', last, afterJoin⟩
          · exact .interior (.base (.conditional (.join joinBlock sourceFuel sourceDone joinStep finalPost)))
          · obtain ⟨lastFuel, actualLast⟩ := runtimeStep_demandInstructionStep last
            have equalLast := actualLast.deterministic (joinStep lastFuel)
            have nextEq : next' = ⟨(joinBlock, 0), final.frame, final.state⟩ := by cases next'; exact equalLast
            subst next'
            apply DemandPrefixDecomposition.complete (sourceFuel := sourceFuel) (value := .normal .unit)
              (consumed := consumed + (branchCount + 1) + 1) (remaining := rest')
              (boundary := ⟨(joinBlock, 0), final.frame, final.state⟩)
            · omega
            · exact (executed.append (.next first branchExecuted)).append (.next last (.zero _))
            · exact afterJoin
            · simp [bind_apply, sourceDone, prepareLoopFlow, prepareReturn, pure_apply]
            · exact finalPost

#print axioms accepted_generated_recursive_if_none_prefix_family
end Goose.Lower

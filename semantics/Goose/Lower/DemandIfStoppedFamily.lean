import Goose.Lower.DemandIfThenProgress

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_if_none_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (condition : Expr) (yes : Core.Block) (origin : OriginId)
    (fragment : ∀ state : St, ScalarAssignmentStatements cfg
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (noValue : yes.value = none)
    (conditionFamily : GeneratedStoppedExpressionPrefixFamily cx results selected none condition) :
    GeneratedStoppedStatementPrefixFamily cx results selected none (.ifS condition yes none origin) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps targetFuel stop after stopped nonTimeout
  obtain ⟨child, childType, canonical, progress⟩ := accepted_generated_if_condition_stopped source selected owned occurrence
    rows coverage admitted bounded realized input extended conditionFamily steps stopped nonTimeout
  cases progress with
  | aborted fuel done =>
    have raw := if_condition_stop (yes := yes) (no := none) (origin := origin) done
    exact .aborted (fuel + 1) (by simp [bind_apply, raw])
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
    have expected := generated_if_branch_step (state := current.state) boolean forkRun boundary.post.pp forkExtended cell targetFuel
    rcases residual.uncons with ⟨_, rfl⟩ | ⟨rest, next, restCount, first, suffix⟩
    · exact (stopped.excludes_step_nonTimeout nonTimeout expected).elim
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
          have same := (branchStep targetFuel).deterministic expected
          exact congrArg (fun point : DemandRuntimePoint => point.point.1) same
        subst actualJoin
        apply StoppedStatementPrefix.complete (flow := .normal .unit) (fuel := fuel + 1)
          (consumed := consumed + 1) (remaining := rest)
          (boundary := ⟨(joinBlock, 0), current.frame, current.state⟩)
        · omega
        · exact executed.append (.next first (.zero _))
        · exact suffix
        · simp [bind_apply, sourceDone, prepareLoopFlow, prepareReturn, pure_apply]
        · exact finalPost
      | true =>
        have branchProgress := accepted_generated_if_then_stopped source child canonical evaluated selected owned occurrence rows
          coverage admitted input boundary forkRun forkExtended startEq branchRun branchExtended jumpRun jumpExtended
          finalEq joinPoint joinStack joinVals (fragment current.state) noValue suffix stopped nonTimeout
        rcases branchProgress with ⟨sourceFuel, sourceStopped⟩ | ⟨branchCount, remaining, final, sourceFuel, branchCountEq, branchExecuted, branchResidual, sourceDone, finalPost⟩
        · exact .aborted sourceFuel (by simp [bind_apply, sourceStopped])
        · apply StoppedStatementPrefix.complete (flow := .normal .unit) (fuel := sourceFuel)
            (consumed := consumed + (branchCount + 1)) (remaining := remaining) (boundary := final)
          · omega
          · exact executed.append (.next first branchExecuted)
          · exact branchResidual
          · simp [bind_apply, sourceDone, prepareLoopFlow, prepareReturn, pure_apply]
          · exact finalPost

#print axioms accepted_generated_if_none_stopped_family
end Goose.Lower

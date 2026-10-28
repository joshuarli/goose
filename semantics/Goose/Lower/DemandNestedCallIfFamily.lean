import Goose.Lower.DemandWhileCallStoppedFamily
import Goose.Lower.DemandIfRecursiveLoopBranches

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_nested_call_if_none_prefix_family {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat} (loop : Option LoopCtx)
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (depth : Nat) (condition : Expr) (yes : Core.Block) (origin : OriginId)
    (fragment : ∀ state : St, BoundedNestedCallLoopStatements cfg depth
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (branchFamily : ∀ (state : St) (before : LS),
      ReachableSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop [] false yes yes.stmts
        (@NestedCallLoopCursor cfg caller results root owner depth { env with scopes := (yes.scope, state.nextScope) :: env.scopes } loop selected) ∧
      ReachableStoppedSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop [] false yes yes.stmts)
    (noValue : yes.value = none)
    (conditionFamily : GeneratedExpressionPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop condition (@GeneratedControlProgressCursor cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩)) :
    ReachableStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop (.ifS condition yes none origin)
      (@NestedCallLoopCursor cfg caller results root owner (depth + 1) env loop selected) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended callerStart taken reached steps
  refine ⟨owned, coverage, ?_⟩
  obtain ⟨child, childType, canonical, progress⟩ := accepted_generated_if_condition_prefix source selected owned occurrence
    rows coverage admitted bounded realized input extended conditionFamily steps
  cases progress with
  | interior cursor => exact .interior (.conditional (.condition child canonical cursor.demanded cursor.progress))
  | @complete fuel consumed remaining current value count executed residual evaluated boundary =>
    have typed := (child.result fuel value evaluated).typed
    rw [childType] at typed
    obtain ⟨boolean, rfl⟩ := hasTy_bool typed
    have lowered : lowerStmt loop (.ifS condition yes none origin) (lowerEnv cfg.mod env.vars results) before =
        ((), (lowerStmt loop (.ifS condition yes none origin) (lowerEnv cfg.mod env.vars results) before).2) := by
      generalize run : lowerStmt loop (.ifS condition yes none origin) (lowerEnv cfg.mod env.vars results) before = output
      cases output with
      | mk returned builder => cases returned; rfl
    obtain ⟨yesBlock, joinBlock, forked, branchStart, branchEnd, jumped, result, forkRun, startEq,
      branchRun, jumpRun, finalEq, forkExtended, branchExtended, jumpExtended, joinPoint, joinStack, joinVals⟩ :=
      generated_if_none_join_builder lowered boundary.post.pp extended
    have cell := boundary.post.has ((lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1, .val (.bool boolean)) (by simp)
    rcases residual.uncons with ⟨_, rfl⟩ | ⟨rest, next, restCount, first, suffix⟩
    · have step : ∃ next, ∀ targetFuel, DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ targetFuel reached next := by
        refine ⟨⟨(if boolean then yesBlock else joinBlock, 0), reached.frame, reached.state⟩, ?_⟩
        intro targetFuel
        exact generated_if_branch_step boolean forkRun boundary.post.pp forkExtended cell targetFuel
      exact .interior (.conditional (.fork child boolean fuel canonical evaluated boundary step))
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
        · cases loop <;> simp [bind_apply, sourceDone, prepareLoopFlow, prepareReturn, prepareLoopExit, pure_apply]
        · exact finalPost
      | true =>
        have branchProgress := accepted_generated_if_invariant_then_prefix_canonical source child canonical evaluated selected owned occurrence rows
          coverage admitted input boundary forkRun forkExtended startEq branchRun branchExtended jumpRun jumpExtended
          finalEq joinPoint joinStack joinVals _
          (fun point => Evidence.RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point.point point.frame point.state)
          (fun valid steps => steps.reachable valid) ((executed.append (.next first (.zero _))).reachable callerStart)
          (branchFamily current.state branchStart).1
          (fun done => (fragment current.state).recursive.normal_any_env done) noValue suffix
        rcases branchProgress with ⟨branch, branchCanonical, demanded⟩ | ⟨branchCount, remaining, final, sourceFuel, branchCountEq, branchExecuted, branchResidual, sourceDone, joinStep, finalPost⟩
        · exact .interior (.conditional (.branch child true fuel canonical evaluated rfl
          (by simp [DemandNode.child?, DemandNode.children]) branch branchCanonical demanded))
        · rcases branchResidual.uncons with ⟨_, rfl⟩ | ⟨rest', next', restCount', last, afterJoin⟩
          · exact .interior (.conditional (.join joinBlock sourceFuel sourceDone joinStep finalPost))
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
            · cases loop <;> simp [bind_apply, sourceDone, prepareLoopFlow, prepareReturn, prepareLoopExit, pure_apply]
            · exact finalPost


theorem accepted_generated_nested_call_if_none_stopped_family {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat} (loop : Option LoopCtx)
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (depth : Nat) (condition : Expr) (yes : Core.Block) (origin : OriginId)
    (fragment : ∀ state : St, BoundedNestedCallLoopStatements cfg depth
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (branchFamily : ∀ (state : St) (before : LS),
      ReachableSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop [] false yes yes.stmts
        (@NestedCallLoopCursor cfg caller results root owner depth { env with scopes := (yes.scope, state.nextScope) :: env.scopes } loop selected) ∧
      ReachableStoppedSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop [] false yes yes.stmts)
    (noValue : yes.value = none)
    (conditionFamily : GeneratedStoppedExpressionPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop condition) :
    ReachableStoppedStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop (.ifS condition yes none origin) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended callerStart taken reached steps targetFuel stop after stopped nonTimeout
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
    have lowered : lowerStmt loop (.ifS condition yes none origin) (lowerEnv cfg.mod env.vars results) before =
        ((), (lowerStmt loop (.ifS condition yes none origin) (lowerEnv cfg.mod env.vars results) before).2) := by
      generalize run : lowerStmt loop (.ifS condition yes none origin) (lowerEnv cfg.mod env.vars results) before = output
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
        · cases loop <;> simp [bind_apply, sourceDone, prepareLoopFlow, prepareReturn, prepareLoopExit, pure_apply]
        · exact finalPost
      | true =>
        have branchProgress := accepted_generated_if_invariant_then_stopped source child canonical evaluated selected owned occurrence rows
          coverage admitted input boundary forkRun forkExtended startEq branchRun branchExtended jumpRun jumpExtended
          finalEq joinPoint joinStack joinVals
          (fun point => Evidence.RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point.point point.frame point.state)
          (fun valid steps => steps.reachable valid) ((executed.append (.next first (.zero _))).reachable callerStart)
          (branchFamily current.state branchStart).2
          (fun done => (fragment current.state).recursive.normal_any_env done) noValue suffix stopped nonTimeout
        rcases branchProgress with ⟨sourceFuel, sourceStopped⟩ | ⟨branchCount, remaining, final, sourceFuel, branchCountEq, branchExecuted, branchResidual, sourceDone, finalPost⟩
        · exact .aborted sourceFuel (by simp [bind_apply, sourceStopped])
        · apply StoppedStatementPrefix.complete (flow := .normal .unit) (fuel := sourceFuel)
            (consumed := consumed + (branchCount + 1)) (remaining := remaining) (boundary := final)
          · omega
          · exact executed.append (.next first branchExecuted)
          · exact branchResidual
          · cases loop <;> simp [bind_apply, sourceDone, prepareLoopFlow, prepareReturn, prepareLoopExit, pure_apply]
          · exact finalPost


#print axioms accepted_generated_nested_call_if_none_prefix_family
#print axioms accepted_generated_nested_call_if_none_stopped_family
end Goose.Lower

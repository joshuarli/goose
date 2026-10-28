import Goose.Lower.DemandIfRecursiveLoopCursor
import Goose.Lower.DemandIfThenProgress

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_invariant_if_none_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat} (loop : Option LoopCtx)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (condition : Expr) (yes : Core.Block) (origin : OriginId)
    (inner : ∀ {innerEnv : Env}, GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod innerEnv.vars results) root owner →
      ∀ {statement : Stmt} {state : St}, StmtSource cfg innerEnv statement state →
        LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (invariant : DemandRuntimePoint → Prop)
    (advance : ∀ {length : Nat} {first last : DemandRuntimePoint}, invariant first → DemandRuntimePrefix cx length first last → invariant last)
    (branchFamily : ∀ (state : St) (before : LS),
      InvariantSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        cx results selected before loop [] false yes yes.stmts (@inner { env with scopes := (yes.scope, state.nextScope) :: env.scopes } selected) invariant ∧
      InvariantStoppedSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        cx results selected before loop [] false yes yes.stmts invariant)
    (normal : ∀ (middle : St) {fuel : Nat} {state after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts state = .ok flow after → flow = .normal .unit)
    (noValue : yes.value = none)
    (conditionFamily : GeneratedExpressionPrefixFamily cx results selected loop condition (@GeneratedControlProgressCursor cfg env cx)) :
    InvariantStatementPrefixFamily cx results selected loop (.ifS condition yes none origin)
      (@RecursiveLoopIfCursorStep cfg cx results root owner loop inner env selected) invariant := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended callerStart taken reached steps
  refine ⟨owned, coverage, ?_⟩
  obtain ⟨child, childType, canonical, progress⟩ := accepted_generated_if_condition_prefix source selected owned occurrence
    rows coverage admitted bounded realized input extended conditionFamily steps
  cases progress with
  | interior cursor => exact .interior (.condition child canonical cursor.demanded cursor.progress)
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
    · have step : ∃ next, ∀ targetFuel, DemandInstructionStep cx targetFuel reached next := by
        refine ⟨⟨(if boolean then yesBlock else joinBlock, 0), reached.frame, reached.state⟩, ?_⟩
        intro targetFuel
        exact generated_if_branch_step boolean forkRun boundary.post.pp forkExtended cell targetFuel
      exact .interior (.fork child boolean fuel canonical evaluated boundary step)
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
          invariant advance (advance callerStart (executed.append (.next first (.zero _))))
          (branchFamily current.state branchStart).1
          (fun done => normal current.state done) noValue suffix
        rcases branchProgress with ⟨branch, branchCanonical, demanded⟩ | ⟨branchCount, remaining, final, sourceFuel, branchCountEq, branchExecuted, branchResidual, sourceDone, joinStep, finalPost⟩
        · exact .interior (.branch child true fuel canonical evaluated rfl
          (by simp [DemandNode.child?, DemandNode.children]) branch branchCanonical demanded)
        · rcases branchResidual.uncons with ⟨_, rfl⟩ | ⟨rest', next', restCount', last, afterJoin⟩
          · exact .interior (.join joinBlock sourceFuel sourceDone joinStep finalPost)
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


theorem accepted_generated_invariant_if_none_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat} (loop : Option LoopCtx)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (condition : Expr) (yes : Core.Block) (origin : OriginId)
    (inner : ∀ {innerEnv : Env}, GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod innerEnv.vars results) root owner →
      ∀ {statement : Stmt} {state : St}, StmtSource cfg innerEnv statement state →
        LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (invariant : DemandRuntimePoint → Prop)
    (advance : ∀ {length : Nat} {first last : DemandRuntimePoint}, invariant first → DemandRuntimePrefix cx length first last → invariant last)
    (branchFamily : ∀ (state : St) (before : LS),
      InvariantSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        cx results selected before loop [] false yes yes.stmts (@inner { env with scopes := (yes.scope, state.nextScope) :: env.scopes } selected) invariant ∧
      InvariantStoppedSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        cx results selected before loop [] false yes yes.stmts invariant)
    (normal : ∀ (middle : St) {fuel : Nat} {state after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts state = .ok flow after → flow = .normal .unit)
    (noValue : yes.value = none)
    (conditionFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop condition) :
    InvariantStoppedStatementPrefixFamily cx results selected loop (.ifS condition yes none origin) invariant := by
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
          invariant advance (advance callerStart (executed.append (.next first (.zero _))))
          (branchFamily current.state branchStart).2
          (fun done => normal current.state done) noValue suffix stopped nonTimeout
        rcases branchProgress with ⟨sourceFuel, sourceStopped⟩ | ⟨branchCount, remaining, final, sourceFuel, branchCountEq, branchExecuted, branchResidual, sourceDone, finalPost⟩
        · exact .aborted sourceFuel (by simp [bind_apply, sourceStopped])
        · apply StoppedStatementPrefix.complete (flow := .normal .unit) (fuel := sourceFuel)
            (consumed := consumed + (branchCount + 1)) (remaining := remaining) (boundary := final)
          · omega
          · exact executed.append (.next first branchExecuted)
          · exact branchResidual
          · cases loop <;> simp [bind_apply, sourceDone, prepareLoopFlow, prepareReturn, prepareLoopExit, pure_apply]
          · exact finalPost


#print axioms accepted_generated_invariant_if_none_prefix_family
#print axioms accepted_generated_invariant_if_none_stopped_family
end Goose.Lower

import Goose.Lower.DemandIfRecursiveLoopCursor
import Goose.Lower.DemandIfThenProgress
import Goose.Lower.DemandIfElseProgress

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_recursive_loop_if_some_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat} (loop : Option LoopCtx)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (depth : Nat) (condition : Expr) (yes no : Core.Block) (origin : OriginId)
    (yesFragment : ∀ state : St, BoundedIfStatements cfg depth
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (noFragment : ∀ state : St, BoundedIfStatements cfg depth
      { env with scopes := (no.scope, state.nextScope) :: env.scopes } no.stmts)
    (yesFamily : RecursiveLoopIfBranchFamily cx results selected loop depth yes)
    (noFamily : RecursiveLoopIfBranchFamily cx results selected loop depth no)
    (yesNoValue : yes.value = none) (noNoValue : no.value = none)
    (conditionFamily : GeneratedExpressionPrefixFamily cx results selected loop condition (@CanonicalExpressionPrefixCursor cfg env cx)) :
    GeneratedStatementPrefixFamily cx results selected loop (.ifS condition yes (some no) origin)
      (@RecursiveLoopIfCursor cfg cx results root owner loop (depth + 1) env selected) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  refine ⟨owned, coverage, ?_⟩
  obtain ⟨child, childType, canonical, progress⟩ := accepted_generated_if_condition_prefix source selected owned occurrence
    rows coverage admitted bounded realized input extended conditionFamily steps
  cases progress with
  | interior demanded => exact .interior (.condition child canonical demanded)
  | @complete fuel consumed remaining current value count executed residual evaluated boundary =>
    have typed := (child.result fuel value evaluated).typed
    rw [childType] at typed
    obtain ⟨boolean, rfl⟩ := hasTy_bool typed
    have lowered : lowerStmt loop (.ifS condition yes (some no) origin) (lowerEnv cfg.mod env.vars results) before =
        ((), (lowerStmt loop (.ifS condition yes (some no) origin) (lowerEnv cfg.mod env.vars results) before).2) := by
      generalize run : lowerStmt loop (.ifS condition yes (some no) origin) (lowerEnv cfg.mod env.vars results) before = output
      cases output with
      | mk returned builder => cases returned; rfl
    obtain ⟨yesBlock, noBlock, forked, yesStart, yesEnd, noStart, noEnd, yesValue, noValue, yesEndPoint, noEndPoint,
      forkRun, yesStartEq, yesRun, yesCurrent, noStartEq, noRun, noCurrent, joined, forkExtended, yesExtended, noExtended⟩ :=
      generated_if_some_fork lowered boundary.post.pp extended
    have cell := boundary.post.has ((lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1, .val (.bool boolean)) (by simp)
    rcases residual.uncons with ⟨_, rfl⟩ | ⟨rest, next, restCount, first, suffix⟩
    · exact .interior (.fork child boolean fuel canonical evaluated boundary)
    · obtain ⟨stepFuel, actual⟩ := runtimeStep_demandInstructionStep first
      have equal := actual.deterministic (generated_if_branch_step (state := current.state) boolean forkRun boundary.post.pp forkExtended cell stepFuel)
      have nextEq : next = ⟨(if boolean then yesBlock else noBlock, 0), current.frame, current.state⟩ := by
        cases next
        exact equal
      subst next
      have branchForm : BoundedIfStatements cfg depth
          { env with scopes := ((if boolean then yes else no).scope, current.state.nextScope) :: env.scopes }
          (if boolean then yes else no).stmts := by
        cases boolean <;> first | exact noFragment current.state | exact yesFragment current.state
      have branchNoValue : (if boolean then yes else no).value = none := by cases boolean <;> assumption
      have bodyFamily : GeneratedSequencePrefixFamily
          (env := { env with scopes := ((if boolean then yes else no).scope, current.state.nextScope) :: env.scopes })
          cx results selected (if boolean then yesStart else noStart) loop [] false (if boolean then yes else no)
          (if boolean then yes else no).stmts
          (@RecursiveLoopIfCursor cfg cx results root owner loop depth
            { env with scopes := ((if boolean then yes else no).scope, current.state.nextScope) :: env.scopes } selected) := by
        cases boolean
        · exact (noFamily current.state noStart).1
        · exact (yesFamily current.state yesStart).1
      have branchProgress := accepted_generated_if_generic_selected_prefix_canonical source child canonical boolean evaluated selected owned occurrence rows
        coverage admitted input boundary forkRun forkExtended yesStartEq yesRun yesCurrent yesExtended noStartEq noRun noCurrent noExtended
        joined extended _ bodyFamily (fun done => branchForm.recursive.normal done) branchNoValue suffix
      rcases branchProgress with ⟨branch, ⟨index, found, indexEq, branchCanonical⟩, demanded⟩ | ⟨branchCount, remaining, final, sourceFuel, branchCountEq, branchExecuted, branchResidual, sourceDone, joinStep, finalPost⟩
      · exact .interior (.branch child boolean fuel canonical evaluated indexEq found branch branchCanonical demanded)
      · rcases branchResidual.uncons with ⟨_, rfl⟩ | ⟨rest', next', restCount', last, afterJoin⟩
        · exact .interior (.join noEnd.blocks.size sourceFuel sourceDone joinStep finalPost)
        · obtain ⟨lastFuel, actualLast⟩ := runtimeStep_demandInstructionStep last
          have equalLast := actualLast.deterministic (joinStep lastFuel)
          have nextEq : next' = ⟨(noEnd.blocks.size, 0), final.frame, final.state⟩ := by cases next'; exact equalLast
          subst next'
          apply DemandPrefixDecomposition.complete (sourceFuel := sourceFuel) (value := .normal .unit)
            (consumed := consumed + (branchCount + 1) + 1) (remaining := rest')
            (boundary := ⟨(noEnd.blocks.size, 0), final.frame, final.state⟩)
          · omega
          · exact (executed.append (.next first branchExecuted)).append (.next last (.zero _))
          · exact afterJoin
          · cases loop <;> simp [bind_apply, sourceDone, prepareLoopFlow, prepareReturn, prepareLoopExit, pure_apply]
          · exact finalPost



theorem accepted_generated_recursive_loop_if_some_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat} (loop : Option LoopCtx)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (depth : Nat) (condition : Expr) (yes no : Core.Block) (origin : OriginId)
    (yesFragment : ∀ state : St, BoundedIfStatements cfg depth
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (noFragment : ∀ state : St, BoundedIfStatements cfg depth
      { env with scopes := (no.scope, state.nextScope) :: env.scopes } no.stmts)
    (yesFamily : RecursiveLoopIfBranchFamily cx results selected loop depth yes)
    (noFamily : RecursiveLoopIfBranchFamily cx results selected loop depth no)
    (yesNoValue : yes.value = none) (noNoValue : no.value = none)
    (conditionFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop condition) :
    GeneratedStoppedStatementPrefixFamily cx results selected loop (.ifS condition yes (some no) origin) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps targetFuel stop after stopped nonTimeout
  obtain ⟨child, childType, canonical, progress⟩ := accepted_generated_if_condition_stopped source selected owned occurrence
    rows coverage admitted bounded realized input extended conditionFamily steps stopped nonTimeout
  cases progress with
  | aborted fuel done =>
    have raw := if_condition_stop (yes := yes) (no := some no) (origin := origin) done
    exact .aborted (fuel + 1) (by simp [bind_apply, raw])
  | @complete fuel consumed remaining current value count executed residual evaluated boundary =>
    have typed := (child.result fuel value evaluated).typed
    rw [childType] at typed
    obtain ⟨boolean, rfl⟩ := hasTy_bool typed
    have lowered : lowerStmt loop (.ifS condition yes (some no) origin) (lowerEnv cfg.mod env.vars results) before =
        ((), (lowerStmt loop (.ifS condition yes (some no) origin) (lowerEnv cfg.mod env.vars results) before).2) := by
      generalize run : lowerStmt loop (.ifS condition yes (some no) origin) (lowerEnv cfg.mod env.vars results) before = output
      cases output with
      | mk returned builder => cases returned; rfl
    obtain ⟨yesBlock, noBlock, forked, yesStart, yesEnd, noStart, noEnd, yesValue, noValue, yesEndPoint, noEndPoint,
      forkRun, yesStartEq, yesRun, yesCurrent, noStartEq, noRun, noCurrent, joined, forkExtended, yesExtended, noExtended⟩ :=
      generated_if_some_fork lowered boundary.post.pp extended
    have cell := boundary.post.has ((lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1, .val (.bool boolean)) (by simp)
    have expected := generated_if_branch_step (state := current.state) boolean forkRun boundary.post.pp forkExtended cell targetFuel
    rcases residual.uncons with ⟨_, rfl⟩ | ⟨rest, next, restCount, first, suffix⟩
    · exact (stopped.excludes_step_nonTimeout nonTimeout expected).elim
    · obtain ⟨stepFuel, actual⟩ := runtimeStep_demandInstructionStep first
      have equal := actual.deterministic (generated_if_branch_step (state := current.state) boolean forkRun boundary.post.pp forkExtended cell stepFuel)
      have nextEq : next = ⟨(if boolean then yesBlock else noBlock, 0), current.frame, current.state⟩ := by cases next; exact equal
      subst next
      have branchForm : BoundedIfStatements cfg depth
          { env with scopes := ((if boolean then yes else no).scope, current.state.nextScope) :: env.scopes }
          (if boolean then yes else no).stmts := by
        cases boolean <;> first | exact noFragment current.state | exact yesFragment current.state
      have branchNoValue : (if boolean then yes else no).value = none := by cases boolean <;> assumption
      have bodyFamily : GeneratedStoppedSequencePrefixFamily
          (env := { env with scopes := ((if boolean then yes else no).scope, current.state.nextScope) :: env.scopes })
          cx results selected (if boolean then yesStart else noStart) loop [] false (if boolean then yes else no)
          (if boolean then yes else no).stmts := by
        cases boolean
        · exact (noFamily current.state noStart).2
        · exact (yesFamily current.state yesStart).2
      have branchProgress := accepted_generated_if_generic_selected_stopped source child canonical boolean evaluated selected owned occurrence rows
        coverage admitted input boundary forkRun forkExtended yesStartEq yesRun yesCurrent yesExtended noStartEq noRun noCurrent noExtended
        joined extended bodyFamily (fun done => branchForm.recursive.normal done) branchNoValue suffix stopped nonTimeout
      rcases branchProgress with ⟨sourceFuel, sourceStopped⟩ | ⟨branchCount, remaining, final, sourceFuel, branchCountEq, branchExecuted, branchResidual, sourceDone, finalPost⟩
      · exact .aborted sourceFuel (by simp [bind_apply, sourceStopped])
      · apply StoppedStatementPrefix.complete (flow := .normal .unit) (fuel := sourceFuel)
          (consumed := consumed + (branchCount + 1)) (remaining := remaining) (boundary := final)
        · omega
        · exact executed.append (.next first branchExecuted)
        · exact branchResidual
        · cases loop <;> simp [bind_apply, sourceDone, prepareLoopFlow, prepareReturn, prepareLoopExit, pure_apply]
        · exact finalPost



theorem accepted_generated_recursive_loop_if_none_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat} (loop : Option LoopCtx)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (depth : Nat) (condition : Expr) (yes : Core.Block) (origin : OriginId)
    (fragment : ∀ state : St, BoundedIfStatements cfg depth
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (branchFamily : RecursiveLoopIfBranchFamily cx results selected loop depth yes)
    (noValue : yes.value = none)
    (conditionFamily : GeneratedExpressionPrefixFamily cx results selected loop condition (@CanonicalExpressionPrefixCursor cfg env cx)) :
    GeneratedStatementPrefixFamily cx results selected loop (.ifS condition yes none origin)
      (@RecursiveLoopIfCursor cfg cx results root owner loop (depth + 1) env selected) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  refine ⟨owned, coverage, ?_⟩
  obtain ⟨child, childType, canonical, progress⟩ := accepted_generated_if_condition_prefix source selected owned occurrence
    rows coverage admitted bounded realized input extended conditionFamily steps
  cases progress with
  | interior demanded => exact .interior (.condition child canonical demanded)
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
    · exact .interior (.fork child boolean fuel canonical evaluated boundary)
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
        have branchProgress := accepted_generated_if_generic_then_prefix_canonical source child canonical evaluated selected owned occurrence rows
          coverage admitted input boundary forkRun forkExtended startEq branchRun branchExtended jumpRun jumpExtended
          finalEq joinPoint joinStack joinVals _ (branchFamily current.state branchStart).1
          (fun done => (fragment current.state).recursive.normal done) noValue suffix
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


theorem accepted_generated_recursive_loop_if_none_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat} (loop : Option LoopCtx)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (depth : Nat) (condition : Expr) (yes : Core.Block) (origin : OriginId)
    (fragment : ∀ state : St, BoundedIfStatements cfg depth
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (branchFamily : RecursiveLoopIfBranchFamily cx results selected loop depth yes)
    (noValue : yes.value = none)
    (conditionFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop condition) :
    GeneratedStoppedStatementPrefixFamily cx results selected loop (.ifS condition yes none origin) := by
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
        have branchProgress := accepted_generated_if_generic_then_stopped source child canonical evaluated selected owned occurrence rows
          coverage admitted input boundary forkRun forkExtended startEq branchRun branchExtended jumpRun jumpExtended
          finalEq joinPoint joinStack joinVals (branchFamily current.state branchStart).2
          (fun done => (fragment current.state).recursive.normal done) noValue suffix stopped nonTimeout
        rcases branchProgress with ⟨sourceFuel, sourceStopped⟩ | ⟨branchCount, remaining, final, sourceFuel, branchCountEq, branchExecuted, branchResidual, sourceDone, finalPost⟩
        · exact .aborted sourceFuel (by simp [bind_apply, sourceStopped])
        · apply StoppedStatementPrefix.complete (flow := .normal .unit) (fuel := sourceFuel)
            (consumed := consumed + (branchCount + 1)) (remaining := remaining) (boundary := final)
          · omega
          · exact executed.append (.next first branchExecuted)
          · exact branchResidual
          · cases loop <;> simp [bind_apply, sourceDone, prepareLoopFlow, prepareReturn, prepareLoopExit, pure_apply]
          · exact finalPost


#print axioms accepted_generated_recursive_loop_if_some_prefix_family
#print axioms accepted_generated_recursive_loop_if_some_stopped_family
#print axioms accepted_generated_recursive_loop_if_none_prefix_family
#print axioms accepted_generated_recursive_loop_if_none_stopped_family
end Goose.Lower

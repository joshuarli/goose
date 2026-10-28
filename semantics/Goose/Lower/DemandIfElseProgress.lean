import Goose.Lower.DemandIfElseSelection

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_if_selected_stopped {cfg : Cfg} {env : Env} {condition : Expr} {yes no : Core.Block}
    {origin : OriginId} {state middle after : St} (source : StmtSource cfg env (.ifS condition yes (some no) origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    (takeYes : Bool) {conditionFuel : Nat} (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool takeYes) middle)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    {before forked yesStart yesEnd noStart noEnd built : LS} {initial conditionFrame : GIR.Frame} {start conditionPoint : Pt}
    {map required : RetainedSsaMap} {yesBlock noBlock yesValue noValue : Nat} {yesEndPoint noEndPoint : Option BlockId}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement none (.ifS condition yes (some no) origin)) before)
    (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv before initial start)
    (boundary : ExpressionDemandBoundary child map cx before initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (.bool takeYes) middle conditionPoint conditionFrame)
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 =
      ((yesBlock, noBlock), forked))
    (forkExtended : ExtT forked cx.fn.blocks) (yesStartEq : yesStart = { forked with cur := some yesBlock })
    (yesRun : lowerBlock none [] false yes (lowerEnv cfg.mod env.vars results) yesStart = (yesValue, yesEnd))
    (yesCurrent : yesEndPoint = yesEnd.cur) (yesExtended : ExtT yesEnd cx.fn.blocks)
    (noStartEq : noStart = { yesEnd with cur := some noBlock })
    (noRun : lowerBlock none [] false no (lowerEnv cfg.mod env.vars results) noStart = (noValue, noEnd))
    (noCurrent : noEndPoint = noEnd.cur) (noExtended : ExtT noEnd cx.fn.blocks)
    (joined : joinArms yesEndPoint noEndPoint (lowerEnv cfg.mod env.vars results) noEnd = ((), built))
    (extended : ExtT built cx.fn.blocks)
    (fragment : ScalarAssignmentStatements cfg
      { env with scopes := ((if takeYes then yes else no).scope, middle.nextScope) :: env.scopes }
      (if takeYes then yes else no).stmts)
    (noTail : (if takeYes then yes else no).value = none) {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨(if takeYes then yesBlock else noBlock, 0), conditionFrame, middle⟩ reached)
    {targetFuel : Nat} {stop : Stop} (stopped : DemandInstructionStop cx targetFuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    (∃ fuel, execStmt fuel cfg env (.ifS condition yes (some no) origin) state = .stop stop after) ∨
      ∃ consumed remaining boundaryPoint fuel,
        consumed + remaining = taken ∧
        DemandRuntimePrefix cx consumed ⟨(if takeYes then yesBlock else noBlock, 0), conditionFrame, middle⟩ boundaryPoint ∧
        DemandRuntimePrefix cx remaining boundaryPoint reached ∧
        execStmt fuel cfg env (.ifS condition yes (some no) origin) state = .ok (.normal .unit) boundaryPoint.state ∧
        GeneratedStatementPrefixEnd source map cx before initial built none (.normal .unit) boundaryPoint := by
  obtain ⟨branch, world, branchOwner, branchAdmitted, branchBounded, branchRealized, branchInput, branchOccurrence, branchRows⟩ :=
    accepted_generated_if_selected_input source child canonical takeYes conditionDone selected owned occurrence rows admitted input boundary
      forkRun forkExtended yesStartEq yesRun noStartEq
  have selectedRun : (lowerBlock none [] false (if takeYes then yes else no) (lowerEnv cfg.mod env.vars results)
      (if takeYes then yesStart else noStart)).2 = (if takeYes then yesEnd else noEnd) := by
    cases takeYes <;> simp [yesRun, noRun]
  have branchExtended : ExtT (lowerBlock none [] false (if takeYes then yes else no) (lowerEnv cfg.mod env.vars results)
      (if takeYes then yesStart else noStart)).2 cx.fn.blocks := by
    rw [selectedRun]
    cases takeYes <;> assumption
  have progress := accepted_generated_scalar_branch_block_stopped branch selected branchOwner branchOccurrence branchRows
    coverage branchAdmitted branchBounded branchRealized branchInput branchExtended fragment noTail steps stopped nonTimeout
  cases progress with
  | aborted fuel branchStopped =>
    apply Or.inl
    cases takeYes
    · exact if_else_source_stop (yes := yes) (origin := origin) conditionDone branchStopped nonTimeout
    · exact if_then_source_stop (no := some no) (origin := origin) conditionDone branchStopped nonTimeout
  | @complete fuel consumed remaining current flow count executed residual branchDone ended =>
    have normal := ended.normal
    subst flow
    have combined := accepted_generated_if_some_join source takeYes branch world conditionDone branchDone boundary.post
      forkRun forkExtended yesStartEq yesRun yesCurrent noStartEq noRun noCurrent joined extended ended
    obtain ⟨joinStep, ⟨sourceFuel, sourceDone⟩, finalPost⟩ := combined
    rcases residual.uncons with ⟨_, rfl⟩ | ⟨rest, next, restCount, nextStep, afterJoin⟩
    · exact (stopped.excludes_step_nonTimeout nonTimeout (joinStep targetFuel)).elim
    · obtain ⟨stepFuel, actual⟩ := runtimeStep_demandInstructionStep nextStep
      have equal := actual.deterministic (joinStep stepFuel)
      have nextEq : next = ⟨(noEnd.blocks.size, 0), current.frame, current.state⟩ := by cases next; exact equal
      subst next
      exact Or.inr ⟨consumed + 1, rest, _, sourceFuel, by omega,
        executed.append (.next nextStep (.zero _)), afterJoin, sourceDone, finalPost⟩

theorem accepted_generated_if_selected_prefix {cfg : Cfg} {env : Env} {condition : Expr} {yes no : Core.Block}
    {origin : OriginId} {state middle : St} (source : StmtSource cfg env (.ifS condition yes (some no) origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    (takeYes : Bool) {conditionFuel : Nat} (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool takeYes) middle)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    {before forked yesStart yesEnd noStart noEnd built : LS} {initial conditionFrame : GIR.Frame} {start conditionPoint : Pt}
    {map required : RetainedSsaMap} {yesBlock noBlock yesValue noValue : Nat} {yesEndPoint noEndPoint : Option BlockId}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement none (.ifS condition yes (some no) origin)) before)
    (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv before initial start)
    (boundary : ExpressionDemandBoundary child map cx before initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (.bool takeYes) middle conditionPoint conditionFrame)
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 =
      ((yesBlock, noBlock), forked))
    (forkExtended : ExtT forked cx.fn.blocks) (yesStartEq : yesStart = { forked with cur := some yesBlock })
    (yesRun : lowerBlock none [] false yes (lowerEnv cfg.mod env.vars results) yesStart = (yesValue, yesEnd))
    (yesCurrent : yesEndPoint = yesEnd.cur) (yesExtended : ExtT yesEnd cx.fn.blocks)
    (noStartEq : noStart = { yesEnd with cur := some noBlock })
    (noRun : lowerBlock none [] false no (lowerEnv cfg.mod env.vars results) noStart = (noValue, noEnd))
    (noCurrent : noEndPoint = noEnd.cur) (noExtended : ExtT noEnd cx.fn.blocks)
    (joined : joinArms yesEndPoint noEndPoint (lowerEnv cfg.mod env.vars results) noEnd = ((), built))
    (extended : ExtT built cx.fn.blocks)
    (fragment : ScalarAssignmentStatements cfg
      { env with scopes := ((if takeYes then yes else no).scope, middle.nextScope) :: env.scopes }
      (if takeYes then yes else no).stmts)
    (noTail : (if takeYes then yes else no).value = none) {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨(if takeYes then yesBlock else noBlock, 0), conditionFrame, middle⟩ reached)
    : (∃ branch : BlockSource cfg env [] (if takeYes then yes else no) middle,
        GeneratedScalarAssignmentBlockPrefixDemand branch selected map required (if takeYes then yesStart else noStart) none conditionFrame
          (GeneratedClearBlockDemand branch map required cx results (if takeYes then yesStart else noStart) none conditionFrame) reached) ∨
      ∃ consumed remaining current fuel,
        consumed + remaining = taken ∧
        DemandRuntimePrefix cx consumed ⟨(if takeYes then yesBlock else noBlock, 0), conditionFrame, middle⟩ current ∧
        DemandRuntimePrefix cx remaining current reached ∧
        execStmt fuel cfg env (.ifS condition yes (some no) origin) state = .ok (.normal .unit) current.state ∧
        (∀ targetFuel, DemandInstructionStep cx targetFuel current ⟨(noEnd.blocks.size, 0), current.frame, current.state⟩) ∧
        GeneratedStatementPrefixEnd source map cx before initial built none (.normal .unit)
          ⟨(noEnd.blocks.size, 0), current.frame, current.state⟩ := by
  obtain ⟨branch, world, branchOwner, branchAdmitted, branchBounded, branchRealized, branchInput, branchOccurrence, branchRows⟩ :=
    accepted_generated_if_selected_input source child canonical takeYes conditionDone selected owned occurrence rows admitted input boundary
      forkRun forkExtended yesStartEq yesRun noStartEq
  have selectedRun : (lowerBlock none [] false (if takeYes then yes else no) (lowerEnv cfg.mod env.vars results)
      (if takeYes then yesStart else noStart)).2 = (if takeYes then yesEnd else noEnd) := by
    cases takeYes <;> simp [yesRun, noRun]
  have branchExtended : ExtT (lowerBlock none [] false (if takeYes then yes else no) (lowerEnv cfg.mod env.vars results)
      (if takeYes then yesStart else noStart)).2 cx.fn.blocks := by
    rw [selectedRun]
    cases takeYes <;> assumption
  have progress := accepted_generated_scalar_branch_block_prefix branch fragment selected branchOwner branchOccurrence branchRows
    coverage branchAdmitted branchBounded branchRealized branchInput branchExtended noTail steps
  cases progress.progress with
  | interior demanded => exact Or.inl ⟨branch, demanded⟩
  | @complete fuel consumed remaining current flow count executed residual branchDone ended =>
    have normal := ended.normal
    subst flow
    have combined := accepted_generated_if_some_join source takeYes branch world conditionDone branchDone boundary.post
      forkRun forkExtended yesStartEq yesRun yesCurrent noStartEq noRun noCurrent joined extended ended
    obtain ⟨joinStep, ⟨sourceFuel, sourceDone⟩, finalPost⟩ := combined
    exact Or.inr ⟨consumed, remaining, current, sourceFuel, count, executed, residual, sourceDone, joinStep, finalPost⟩

#print axioms accepted_generated_if_selected_prefix
#print axioms accepted_generated_if_selected_stopped
end Goose.Lower

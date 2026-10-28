import Goose.Lower.DemandIfRecursiveCursor

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_recursive_if_some_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (depth : Nat) (condition : Expr) (yes no : Core.Block) (origin : OriginId)
    (yesFragment : ∀ state : St, BoundedIfStatements cfg depth
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (noFragment : ∀ state : St, BoundedIfStatements cfg depth
      { env with scopes := (no.scope, state.nextScope) :: env.scopes } no.stmts)
    (yesFamily : RecursiveIfBranchFamily cx results selected depth yes)
    (noFamily : RecursiveIfBranchFamily cx results selected depth no)
    (yesNoValue : yes.value = none) (noNoValue : no.value = none)
    (conditionFamily : GeneratedExpressionPrefixFamily cx results selected none condition (@GeneratedControlProgressCursor cfg env cx)) :
    GeneratedStatementPrefixFamily cx results selected none (.ifS condition yes (some no) origin)
      (@RecursiveIfCursor cfg cx results root owner (depth + 1) env selected) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  refine ⟨owned, coverage, ?_⟩
  obtain ⟨child, childType, canonical, progress⟩ := accepted_generated_if_condition_prefix source selected owned occurrence
    rows coverage admitted bounded realized input extended conditionFamily steps
  cases progress with
  | interior cursor => exact .interior (.condition child canonical cursor.demanded cursor.progress)
  | @complete fuel consumed remaining current value count executed residual evaluated boundary =>
    have typed := (child.result fuel value evaluated).typed
    rw [childType] at typed
    obtain ⟨boolean, rfl⟩ := hasTy_bool typed
    have lowered : lowerStmt none (.ifS condition yes (some no) origin) (lowerEnv cfg.mod env.vars results) before =
        ((), (lowerStmt none (.ifS condition yes (some no) origin) (lowerEnv cfg.mod env.vars results) before).2) := by
      generalize run : lowerStmt none (.ifS condition yes (some no) origin) (lowerEnv cfg.mod env.vars results) before = output
      cases output with
      | mk returned builder => cases returned; rfl
    obtain ⟨yesBlock, noBlock, forked, yesStart, yesEnd, noStart, noEnd, yesValue, noValue, yesEndPoint, noEndPoint,
      forkRun, yesStartEq, yesRun, yesCurrent, noStartEq, noRun, noCurrent, joined, forkExtended, yesExtended, noExtended⟩ :=
      generated_if_some_fork lowered boundary.post.pp extended
    have cell := boundary.post.has ((lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1, .val (.bool boolean)) (by simp)
    rcases residual.uncons with ⟨_, rfl⟩ | ⟨rest, next, restCount, first, suffix⟩
    · have step : ∃ next, ∀ targetFuel, DemandInstructionStep cx targetFuel reached next := by
        refine ⟨⟨(if boolean then yesBlock else noBlock, 0), reached.frame, reached.state⟩, ?_⟩
        intro targetFuel
        exact generated_if_branch_step boolean forkRun boundary.post.pp forkExtended cell targetFuel
      exact .interior (.fork child boolean fuel canonical evaluated boundary step)
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
          cx results selected (if boolean then yesStart else noStart) none [] false (if boolean then yes else no)
          (if boolean then yes else no).stmts
          (@RecursiveIfCursor cfg cx results root owner depth
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
          · simp [bind_apply, sourceDone, prepareLoopFlow, prepareReturn, pure_apply]
          · exact finalPost


#print axioms accepted_generated_recursive_if_some_prefix_family
end Goose.Lower

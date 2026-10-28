import Goose.Lower.DemandIfJoin

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_if_invariant_then_stopped {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block}
    {origin : OriginId} {state middle after : St} (source : StmtSource cfg env (.ifS condition yes none origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    {conditionFuel : Nat} (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool true) middle)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    {before forked branchStart branchEnd jumped built : LS} {initial conditionFrame : GIR.Frame} {start conditionPoint : Pt}
    {map required : RetainedSsaMap} {yesBlock joinBlock value : Nat}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.ifS condition yes none origin)) before)
    (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (boundary : ExpressionDemandBoundary child map cx before initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (.bool true) middle conditionPoint conditionFrame)
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 =
      ((yesBlock, joinBlock), forked))
    (forkExtended : ExtT forked cx.fn.blocks) (startEq : branchStart = { forked with cur := some yesBlock })
    (branchRun : lowerBlock loop [] false yes (lowerEnv cfg.mod env.vars results) branchStart = (value, branchEnd))
    (branchExtended : ExtT branchEnd cx.fn.blocks)
    (jumpRun : emitTerm (.br joinBlock []) (lowerEnv cfg.mod env.vars results) branchEnd = ((), jumped))
    (jumpExtended : ExtT jumped cx.fn.blocks) (finalEq : built = { jumped with cur := some joinBlock })
    (joinPoint : built.pp = some (joinBlock, 0))
    (joinStack : built.stack = (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.stack)
    (joinVals : (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.vals.size ≤ built.vals.size)
    (invariant : DemandRuntimePoint → Prop)
    (advance : ∀ {length : Nat} {first last : DemandRuntimePoint}, invariant first → DemandRuntimePrefix cx length first last → invariant last)
    (atStart : invariant ⟨(yesBlock, 0), conditionFrame, middle⟩)
    (bodyFamily : InvariantStoppedSequencePrefixFamily
      (env := { env with scopes := (yes.scope, middle.nextScope) :: env.scopes }) cx results selected branchStart loop [] false yes yes.stmts invariant)
    (normal : ∀ {fuel : Nat} {innerState after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts innerState = .ok flow after →
      flow = .normal .unit)
    (noValue : yes.value = none) {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨(yesBlock, 0), conditionFrame, middle⟩ reached)
    {targetFuel : Nat} {stop : Stop} (stopped : DemandInstructionStop cx targetFuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    (∃ fuel, execStmt fuel cfg env (.ifS condition yes none origin) state = .stop stop after) ∨
      ∃ consumed remaining boundaryPoint fuel,
        consumed + remaining = taken ∧
        DemandRuntimePrefix cx consumed ⟨(yesBlock, 0), conditionFrame, middle⟩ boundaryPoint ∧
        DemandRuntimePrefix cx remaining boundaryPoint reached ∧
        execStmt fuel cfg env (.ifS condition yes none origin) state = .ok (.normal .unit) boundaryPoint.state ∧
        GeneratedStatementPrefixEnd source map cx before initial built loop (.normal .unit) boundaryPoint := by
  obtain ⟨branch, typing, roots, branchCanonical, branchOwner, branchAdmitted, branchBounded, branchRealized, branchInput⟩ :=
    accepted_generated_if_then_input source child canonical conditionDone selected owned admitted input boundary forkRun startEq forkExtended
  obtain ⟨branchOccurrence, branchRows⟩ := generated_if_then_occurrence source branch branchCanonical occurrence rows
    boundary.post.pp forkRun startEq roots
  have finalExtended : ExtT (lowerBlock loop [] false yes (lowerEnv cfg.mod env.vars results) branchStart).2 cx.fn.blocks := by
    rw [branchRun]
    exact branchExtended
  have progress := accepted_generated_invariant_loop_branch_block_stopped branch selected branchOwner branchOccurrence branchRows
    coverage branchAdmitted branchBounded branchRealized branchInput finalExtended invariant advance atStart bodyFamily normal noValue steps stopped nonTimeout
  cases progress with
  | aborted fuel branchStopped =>
    exact Or.inl (if_then_source_stop (no := none) (origin := origin) conditionDone branchStopped nonTimeout)
  | @complete fuel consumed remaining current flow count executed residual branchDone ended =>
    have normal := ended.normal
    subst flow
    have joined := accepted_generated_if_then_join source branch branchCanonical conditionDone branchDone boundary.post
      forkRun forkExtended startEq branchRun jumpRun jumpExtended finalEq joinPoint joinStack joinVals ended
    obtain ⟨joinStep, ⟨sourceFuel, sourceDone⟩, finalPost⟩ := joined
    rcases residual.uncons with ⟨_, rfl⟩ | ⟨rest, next, restCount, nextStep, afterJoin⟩
    · exact (stopped.excludes_step_nonTimeout nonTimeout (joinStep targetFuel)).elim
    · obtain ⟨stepFuel, actual⟩ := runtimeStep_demandInstructionStep nextStep
      have equal := actual.deterministic (joinStep stepFuel)
      have nextEq : next = ⟨(joinBlock, 0), current.frame, current.state⟩ := by
        cases next
        exact equal
      subst next
      exact Or.inr ⟨consumed + 1, rest, _, sourceFuel, by omega,
        executed.append (.next nextStep (.zero _)), afterJoin, sourceDone, finalPost⟩


theorem accepted_generated_if_generic_then_stopped {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block}
    {origin : OriginId} {state middle after : St} (source : StmtSource cfg env (.ifS condition yes none origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    {conditionFuel : Nat} (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool true) middle)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    {before forked branchStart branchEnd jumped built : LS} {initial conditionFrame : GIR.Frame} {start conditionPoint : Pt}
    {map required : RetainedSsaMap} {yesBlock joinBlock value : Nat}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.ifS condition yes none origin)) before)
    (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (boundary : ExpressionDemandBoundary child map cx before initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (.bool true) middle conditionPoint conditionFrame)
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 =
      ((yesBlock, joinBlock), forked))
    (forkExtended : ExtT forked cx.fn.blocks) (startEq : branchStart = { forked with cur := some yesBlock })
    (branchRun : lowerBlock loop [] false yes (lowerEnv cfg.mod env.vars results) branchStart = (value, branchEnd))
    (branchExtended : ExtT branchEnd cx.fn.blocks)
    (jumpRun : emitTerm (.br joinBlock []) (lowerEnv cfg.mod env.vars results) branchEnd = ((), jumped))
    (jumpExtended : ExtT jumped cx.fn.blocks) (finalEq : built = { jumped with cur := some joinBlock })
    (joinPoint : built.pp = some (joinBlock, 0))
    (joinStack : built.stack = (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.stack)
    (joinVals : (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.vals.size ≤ built.vals.size)
    (bodyFamily : GeneratedStoppedSequencePrefixFamily
      (env := { env with scopes := (yes.scope, middle.nextScope) :: env.scopes }) cx results selected branchStart loop [] false yes yes.stmts)
    (normal : ∀ {fuel : Nat} {innerState after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts innerState = .ok flow after →
      flow = .normal .unit)
    (noValue : yes.value = none) {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨(yesBlock, 0), conditionFrame, middle⟩ reached)
    {targetFuel : Nat} {stop : Stop} (stopped : DemandInstructionStop cx targetFuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    (∃ fuel, execStmt fuel cfg env (.ifS condition yes none origin) state = .stop stop after) ∨
      ∃ consumed remaining boundaryPoint fuel,
        consumed + remaining = taken ∧
        DemandRuntimePrefix cx consumed ⟨(yesBlock, 0), conditionFrame, middle⟩ boundaryPoint ∧
        DemandRuntimePrefix cx remaining boundaryPoint reached ∧
        execStmt fuel cfg env (.ifS condition yes none origin) state = .ok (.normal .unit) boundaryPoint.state ∧
        GeneratedStatementPrefixEnd source map cx before initial built loop (.normal .unit) boundaryPoint := by
  have invariantFamily : InvariantStoppedSequencePrefixFamily
      (env := { env with scopes := (yes.scope, middle.nextScope) :: env.scopes }) cx results selected branchStart loop [] false yes yes.stmts (fun _ => True) := by
    intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps fuel stop after stopped nonTimeout
    exact bodyFamily source owned occurrence all scope value rows coverage admitted bounded realized input extended steps stopped nonTimeout
  exact accepted_generated_if_invariant_then_stopped source child canonical conditionDone selected owned occurrence rows coverage admitted
    input boundary forkRun forkExtended startEq branchRun branchExtended jumpRun jumpExtended finalEq joinPoint joinStack joinVals
    (fun _ => True) (fun _ _ => trivial) trivial invariantFamily normal noValue steps stopped nonTimeout


theorem accepted_generated_if_then_stopped {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block}
    {origin : OriginId} {state middle after : St} (source : StmtSource cfg env (.ifS condition yes none origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    {conditionFuel : Nat} (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool true) middle)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    {before forked branchStart branchEnd jumped built : LS} {initial conditionFrame : GIR.Frame} {start conditionPoint : Pt}
    {map required : RetainedSsaMap} {yesBlock joinBlock value : Nat}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement none (.ifS condition yes none origin)) before)
    (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv before initial start)
    (boundary : ExpressionDemandBoundary child map cx before initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (.bool true) middle conditionPoint conditionFrame)
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 =
      ((yesBlock, joinBlock), forked))
    (forkExtended : ExtT forked cx.fn.blocks) (startEq : branchStart = { forked with cur := some yesBlock })
    (branchRun : lowerBlock none [] false yes (lowerEnv cfg.mod env.vars results) branchStart = (value, branchEnd))
    (branchExtended : ExtT branchEnd cx.fn.blocks)
    (jumpRun : emitTerm (.br joinBlock []) (lowerEnv cfg.mod env.vars results) branchEnd = ((), jumped))
    (jumpExtended : ExtT jumped cx.fn.blocks) (finalEq : built = { jumped with cur := some joinBlock })
    (joinPoint : built.pp = some (joinBlock, 0))
    (joinStack : built.stack = (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.stack)
    (joinVals : (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.vals.size ≤ built.vals.size)
    (fragment : ScalarAssignmentStatements cfg { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts)
    (noValue : yes.value = none) {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨(yesBlock, 0), conditionFrame, middle⟩ reached)
    {targetFuel : Nat} {stop : Stop} (stopped : DemandInstructionStop cx targetFuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    (∃ fuel, execStmt fuel cfg env (.ifS condition yes none origin) state = .stop stop after) ∨
      ∃ consumed remaining boundaryPoint fuel,
        consumed + remaining = taken ∧
        DemandRuntimePrefix cx consumed ⟨(yesBlock, 0), conditionFrame, middle⟩ boundaryPoint ∧
        DemandRuntimePrefix cx remaining boundaryPoint reached ∧
        execStmt fuel cfg env (.ifS condition yes none origin) state = .ok (.normal .unit) boundaryPoint.state ∧
        GeneratedStatementPrefixEnd source map cx before initial built none (.normal .unit) boundaryPoint := by
  have bodyFamily : GeneratedStoppedSequencePrefixFamily
      (env := { env with scopes := (yes.scope, middle.nextScope) :: env.scopes }) cx results selected branchStart none [] false yes yes.stmts :=
    (accepted_generated_scalar_assignment_statements_agreement
      (env := { env with scopes := (yes.scope, middle.nextScope) :: env.scopes }) selected branchStart none [] false yes fragment).2
  exact accepted_generated_if_generic_then_stopped source child canonical conditionDone selected owned occurrence rows coverage admitted input boundary forkRun forkExtended startEq
    branchRun branchExtended jumpRun jumpExtended finalEq joinPoint joinStack joinVals
    bodyFamily (fun done => fragment.normal done) noValue steps stopped nonTimeout


theorem accepted_generated_if_invariant_then_prefix_canonical {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block}
    {origin : OriginId} {state middle : St} (source : StmtSource cfg env (.ifS condition yes none origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    {conditionFuel : Nat} (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool true) middle)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    {before forked branchStart branchEnd jumped built : LS} {initial conditionFrame : GIR.Frame} {start conditionPoint : Pt}
    {map required : RetainedSsaMap} {yesBlock joinBlock value : Nat}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.ifS condition yes none origin)) before)
    (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (boundary : ExpressionDemandBoundary child map cx before initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (.bool true) middle conditionPoint conditionFrame)
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 =
      ((yesBlock, joinBlock), forked))
    (forkExtended : ExtT forked cx.fn.blocks) (startEq : branchStart = { forked with cur := some yesBlock })
    (branchRun : lowerBlock loop [] false yes (lowerEnv cfg.mod env.vars results) branchStart = (value, branchEnd))
    (branchExtended : ExtT branchEnd cx.fn.blocks)
    (jumpRun : emitTerm (.br joinBlock []) (lowerEnv cfg.mod env.vars results) branchEnd = ((), jumped))
    (jumpExtended : ExtT jumped cx.fn.blocks) (finalEq : built = { jumped with cur := some joinBlock })
    (joinPoint : built.pp = some (joinBlock, 0))
    (joinStack : built.stack = (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.stack)
    (joinVals : (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.vals.size ≤ built.vals.size)
    (cursor : ∀ {statement : Stmt} {innerState : St}, StmtSource cfg
      { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } statement innerState →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (invariant : DemandRuntimePoint → Prop)
    (advance : ∀ {length : Nat} {first last : DemandRuntimePoint}, invariant first → DemandRuntimePrefix cx length first last → invariant last)
    (atStart : invariant ⟨(yesBlock, 0), conditionFrame, middle⟩)
    (bodyFamily : InvariantSequencePrefixFamily
      (env := { env with scopes := (yes.scope, middle.nextScope) :: env.scopes }) cx results selected branchStart loop [] false yes yes.stmts cursor invariant)
    (normal : ∀ {fuel : Nat} {innerState after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts innerState = .ok flow after →
      flow = .normal .unit)
    (noValue : yes.value = none) {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨(yesBlock, 0), conditionFrame, middle⟩ reached)
    : (∃ branch : BlockSource cfg env [] yes middle,
        source.BlockChildAt branch 1 (by simp [DemandNode.child?, DemandNode.children]) ∧
        GeneratedGenericBlockPrefixDemand branch selected map required branchStart loop conditionFrame cursor
          (GeneratedBranchBlockEffectDemand branch map required cx results branchStart loop conditionFrame) reached) ∨
      ∃ consumed remaining current fuel,
        consumed + remaining = taken ∧
        DemandRuntimePrefix cx consumed ⟨(yesBlock, 0), conditionFrame, middle⟩ current ∧
        DemandRuntimePrefix cx remaining current reached ∧
        execStmt fuel cfg env (.ifS condition yes none origin) state = .ok (.normal .unit) current.state ∧
        (∀ targetFuel, DemandInstructionStep cx targetFuel current ⟨(joinBlock, 0), current.frame, current.state⟩) ∧
        GeneratedStatementPrefixEnd source map cx before initial built loop (.normal .unit)
          ⟨(joinBlock, 0), current.frame, current.state⟩ := by
  obtain ⟨branch, typing, roots, branchCanonical, branchOwner, branchAdmitted, branchBounded, branchRealized, branchInput⟩ :=
    accepted_generated_if_then_input source child canonical conditionDone selected owned admitted input boundary forkRun startEq forkExtended
  obtain ⟨branchOccurrence, branchRows⟩ := generated_if_then_occurrence source branch branchCanonical occurrence rows
    boundary.post.pp forkRun startEq roots
  have finalExtended : ExtT (lowerBlock loop [] false yes (lowerEnv cfg.mod env.vars results) branchStart).2 cx.fn.blocks := by
    rw [branchRun]
    exact branchExtended
  have progress := accepted_generated_invariant_branch_block_prefix branch selected branchOwner branchOccurrence branchRows
    coverage branchAdmitted branchBounded branchRealized branchInput finalExtended cursor invariant advance atStart bodyFamily normal noValue steps
  cases progress.progress with
  | interior demanded => exact Or.inl ⟨branch, branchCanonical, demanded⟩
  | @complete fuel consumed remaining current flow count executed residual branchDone ended =>
    have normal := ended.normal
    subst flow
    have joined := accepted_generated_if_then_join source branch branchCanonical conditionDone branchDone boundary.post
      forkRun forkExtended startEq branchRun jumpRun jumpExtended finalEq joinPoint joinStack joinVals ended
    obtain ⟨joinStep, ⟨sourceFuel, sourceDone⟩, finalPost⟩ := joined
    exact Or.inr ⟨consumed, remaining, current, sourceFuel, count, executed, residual, sourceDone, joinStep, finalPost⟩


theorem accepted_generated_if_generic_then_prefix_canonical {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block}
    {origin : OriginId} {state middle : St} (source : StmtSource cfg env (.ifS condition yes none origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    {conditionFuel : Nat} (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool true) middle)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    {before forked branchStart branchEnd jumped built : LS} {initial conditionFrame : GIR.Frame} {start conditionPoint : Pt}
    {map required : RetainedSsaMap} {yesBlock joinBlock value : Nat}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.ifS condition yes none origin)) before)
    (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (boundary : ExpressionDemandBoundary child map cx before initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (.bool true) middle conditionPoint conditionFrame)
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 =
      ((yesBlock, joinBlock), forked))
    (forkExtended : ExtT forked cx.fn.blocks) (startEq : branchStart = { forked with cur := some yesBlock })
    (branchRun : lowerBlock loop [] false yes (lowerEnv cfg.mod env.vars results) branchStart = (value, branchEnd))
    (branchExtended : ExtT branchEnd cx.fn.blocks)
    (jumpRun : emitTerm (.br joinBlock []) (lowerEnv cfg.mod env.vars results) branchEnd = ((), jumped))
    (jumpExtended : ExtT jumped cx.fn.blocks) (finalEq : built = { jumped with cur := some joinBlock })
    (joinPoint : built.pp = some (joinBlock, 0))
    (joinStack : built.stack = (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.stack)
    (joinVals : (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.vals.size ≤ built.vals.size)
    (cursor : ∀ {statement : Stmt} {innerState : St}, StmtSource cfg
      { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } statement innerState →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (bodyFamily : GeneratedSequencePrefixFamily
      (env := { env with scopes := (yes.scope, middle.nextScope) :: env.scopes }) cx results selected branchStart loop [] false yes yes.stmts cursor)
    (normal : ∀ {fuel : Nat} {innerState after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts innerState = .ok flow after →
      flow = .normal .unit)
    (noValue : yes.value = none) {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨(yesBlock, 0), conditionFrame, middle⟩ reached)
    : (∃ branch : BlockSource cfg env [] yes middle,
        source.BlockChildAt branch 1 (by simp [DemandNode.child?, DemandNode.children]) ∧
        GeneratedGenericBlockPrefixDemand branch selected map required branchStart loop conditionFrame cursor
          (GeneratedBranchBlockEffectDemand branch map required cx results branchStart loop conditionFrame) reached) ∨
      ∃ consumed remaining current fuel,
        consumed + remaining = taken ∧
        DemandRuntimePrefix cx consumed ⟨(yesBlock, 0), conditionFrame, middle⟩ current ∧
        DemandRuntimePrefix cx remaining current reached ∧
        execStmt fuel cfg env (.ifS condition yes none origin) state = .ok (.normal .unit) current.state ∧
        (∀ targetFuel, DemandInstructionStep cx targetFuel current ⟨(joinBlock, 0), current.frame, current.state⟩) ∧
        GeneratedStatementPrefixEnd source map cx before initial built loop (.normal .unit)
          ⟨(joinBlock, 0), current.frame, current.state⟩ := by
  have invariantFamily : InvariantSequencePrefixFamily
      (env := { env with scopes := (yes.scope, middle.nextScope) :: env.scopes }) cx results selected branchStart loop [] false yes yes.stmts cursor (fun _ => True) := by
    intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps
    exact bodyFamily source owned occurrence all scope value rows coverage admitted bounded realized input extended steps
  exact accepted_generated_if_invariant_then_prefix_canonical source child canonical conditionDone selected owned occurrence rows coverage admitted
    input boundary forkRun forkExtended startEq branchRun branchExtended jumpRun jumpExtended finalEq joinPoint joinStack joinVals
    cursor (fun _ => True) (fun _ _ => trivial) trivial invariantFamily normal noValue steps


theorem accepted_generated_if_then_prefix {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block}
    {origin : OriginId} {state middle : St} (source : StmtSource cfg env (.ifS condition yes none origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    {conditionFuel : Nat} (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool true) middle)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    {before forked branchStart branchEnd jumped built : LS} {initial conditionFrame : GIR.Frame} {start conditionPoint : Pt}
    {map required : RetainedSsaMap} {yesBlock joinBlock value : Nat}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement none (.ifS condition yes none origin)) before)
    (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv before initial start)
    (boundary : ExpressionDemandBoundary child map cx before initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (.bool true) middle conditionPoint conditionFrame)
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 =
      ((yesBlock, joinBlock), forked))
    (forkExtended : ExtT forked cx.fn.blocks) (startEq : branchStart = { forked with cur := some yesBlock })
    (branchRun : lowerBlock none [] false yes (lowerEnv cfg.mod env.vars results) branchStart = (value, branchEnd))
    (branchExtended : ExtT branchEnd cx.fn.blocks)
    (jumpRun : emitTerm (.br joinBlock []) (lowerEnv cfg.mod env.vars results) branchEnd = ((), jumped))
    (jumpExtended : ExtT jumped cx.fn.blocks) (finalEq : built = { jumped with cur := some joinBlock })
    (joinPoint : built.pp = some (joinBlock, 0))
    (joinStack : built.stack = (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.stack)
    (joinVals : (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.vals.size ≤ built.vals.size)
    (fragment : ScalarAssignmentStatements cfg { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts)
    (noValue : yes.value = none) {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨(yesBlock, 0), conditionFrame, middle⟩ reached)
    : (∃ branch : BlockSource cfg env [] yes middle,
        GeneratedScalarAssignmentBlockPrefixDemand branch selected map required branchStart none conditionFrame
          (GeneratedBranchBlockEffectDemand branch map required cx results branchStart none conditionFrame) reached) ∨
      ∃ consumed remaining current fuel,
        consumed + remaining = taken ∧
        DemandRuntimePrefix cx consumed ⟨(yesBlock, 0), conditionFrame, middle⟩ current ∧
        DemandRuntimePrefix cx remaining current reached ∧
        execStmt fuel cfg env (.ifS condition yes none origin) state = .ok (.normal .unit) current.state ∧
        (∀ targetFuel, DemandInstructionStep cx targetFuel current ⟨(joinBlock, 0), current.frame, current.state⟩) ∧
        GeneratedStatementPrefixEnd source map cx before initial built none (.normal .unit)
          ⟨(joinBlock, 0), current.frame, current.state⟩ := by
  have bodyFamily : GeneratedSequencePrefixFamily
      (env := { env with scopes := (yes.scope, middle.nextScope) :: env.scopes }) cx results selected branchStart none [] false yes yes.stmts
      (@ScalarAssignmentStatementPrefixCursor cfg { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } cx results) :=
    (accepted_generated_scalar_assignment_statements_agreement
      (env := { env with scopes := (yes.scope, middle.nextScope) :: env.scopes }) selected branchStart none [] false yes fragment).1
  have progress := accepted_generated_if_generic_then_prefix_canonical source child canonical conditionDone selected owned occurrence rows coverage admitted input boundary forkRun forkExtended startEq
    branchRun branchExtended jumpRun jumpExtended finalEq joinPoint joinStack joinVals
    _ bodyFamily (fun done => fragment.normal done) noValue steps
  rcases progress with ⟨branch, _, demanded⟩ | completed
  · cases demanded with
    | emitted cursor => exact Or.inl ⟨branch, .emitted cursor⟩
    | suffix cursor => exact Or.inl ⟨branch, .suffix cursor⟩
    | body canonical cursor => exact Or.inl ⟨branch, .body canonical cursor⟩
  · exact Or.inr completed

#print axioms accepted_generated_if_generic_then_prefix_canonical
#print axioms accepted_generated_if_invariant_then_prefix_canonical
#print axioms accepted_generated_if_generic_then_stopped
#print axioms accepted_generated_if_invariant_then_stopped
#print axioms accepted_generated_if_then_prefix
#print axioms accepted_generated_if_then_stopped
end Goose.Lower

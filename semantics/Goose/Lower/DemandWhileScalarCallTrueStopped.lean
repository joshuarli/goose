import Goose.Lower.DemandWhileNestedCallTrueBody
import Goose.Lower.DemandWhileTrueStopped

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_while_bounded_nested_call_true_stopped {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state middle initialState : St} {count depth : Nat}
    (iterations : WhileIterations cfg env condition body count initialState state) (source : StmtSource cfg env (.while condition body origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    {fuel : Nat} (evaluated : evalExpr fuel cfg env condition state = .ok (.bool true) middle)
    (fragment : BoundedNestedCallLoopStatements cfg depth
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } body.stmts)
    (noValue : body.value = none)
    {cx : FnCtx} {results : List Ty} {loop : Option LoopCtx} {root : DemandNode} {owner : Nat}
    (targetConfig : cx.cfg = ⟨cfg.profile, lower cfg.mod⟩)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (families : ∀ (before : LS) (innerLoop : Option LoopCtx),
      ReachableSequencePrefixFamily (env := { env with scopes := (body.scope, middle.nextScope) :: env.scopes }) cx results selected before innerLoop [] false body body.stmts
        (@NestedCallLoopCursor cfg cx.fn results root owner depth { env with scopes := (body.scope, middle.nextScope) :: env.scopes } innerLoop selected) ∧
      ReachableStoppedSequencePrefixFamily (env := { env with scopes := (body.scope, middle.nextScope) :: env.scopes }) cx results selected before innerLoop [] false body body.stmts)
    (owned : GeneratedSourceOwner selected source.context) {before headerState built : LS}
    {header : BlockId} {initial frame : GIR.Frame} {point : Pt}
    (headerInput : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv headerState initial (header, 0))
    (headerTarget : ∃ block, cx.fn.blocks[header]? = some block ∧ block.params = [])
    (headerId : header = (newBlock [] (lowerEnv cfg.mod env.vars results) before).1.1)
    (headerEq : headerState = demandWhileHeaderBefore (lowerEnv cfg.mod env.vars results) before)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.while condition body origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (headerBounded : map.Bounded headerState.vals.size)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (boundary : ExpressionDemandBoundary child map cx headerState initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1 (.bool true) middle point frame)
    (conditionReach : Evidence.RuntimePoint cx.cfg cx.fn point frame middle)
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) headerState = ((), built)) (extended : ExtT built cx.fn.blocks)

    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨point, frame, middle⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    (∃ sourceFuel, execStmt sourceFuel cfg env (.while condition body origin) initialState = .stop stop after) ∨
    ∃ (consumed remaining : Nat) (current : DemandRuntimePoint)
      (next : StmtSource cfg env (.while condition body origin) current.state),
      WhileIterations cfg env condition body (count + 1) initialState current.state ∧
      consumed + remaining = taken ∧ 0 < consumed ∧ DemandRuntimePrefix cx consumed ⟨point, frame, middle⟩ current ∧
      DemandRuntimePrefix cx remaining current reached ∧
      next.typingEnv = source.typingEnv ∧ next.rootsEnv = source.rootsEnv ∧ next.world = source.world ∧
      next.observation = source.observation ∧ next.plans = source.plans ∧ next.path = source.path ∧ HEq next.context source.context ∧
      GeneratedPrefixInput cfg env cx results loop next.typingEnv next.rootsEnv headerState current.frame (header, 0) ∧
      Post cfg env cx headerState initial headerState current.frame (header, 0) [] ∧
      map.Bounded headerState.vals.size ∧ map.Realizes cfg.mod next.world env ⟨(header, 0), current.frame, current.state⟩ ∧
      current.point = (header, 0) ∧ GeneratedSourceOwner selected next.context ∧
      map.Admitted cfg.mod.profile next.context.retained ∧
      ∃ nextOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root next.path (.statement loop (.while condition body origin)) before,
        GeneratedDemandRows cfg.mod next.rootsEnv.access nextOccurrence required := by
  obtain ⟨bodyBlock, exitBlock, forked, bodyStart, bodyEnd, jumped, value, branch, canonicalBranch,
    forkRun, bodyEq, bodyRun, jumpRun, jumpExtended, branchStep, bodyPrefix, bodyStopped⟩ :=
    accepted_generated_while_bounded_nested_call_true_body source child canonical evaluated fragment noValue targetConfig selected families owned headerInput headerTarget
      headerId headerEq occurrence rows coverage admitted boundary conditionReach lowered extended
  rcases steps.uncons with ⟨zero, rfl⟩ | ⟨remaining, nextPoint, stepCount, first, residual⟩
  · exact (stopped.excludes_step_nonTimeout nonTimeout (branchStep targetFuel)).elim
  · obtain ⟨stepFuel, actual⟩ := runtimeStep_demandInstructionStep first
    have equal := actual.deterministic (branchStep stepFuel)
    have nextEq : nextPoint = ⟨(bodyBlock, 0), frame, middle⟩ := by cases nextPoint; exact equal
    subst nextPoint
    have progress := bodyStopped residual stopped nonTimeout
    rcases accepted_generated_while_body_stopped_outcome iterations evaluated branch progress nonTimeout with
      stoppedSource | ⟨bodyFuel, consumed, rest, current, flow, bodyCount, executed, suffix, bodyDone, ended⟩
    · exact Or.inl stoppedSource
    · have normal := ended.normal
      subst flow
      have forkExtended : ExtT forked cx.fn.blocks := by
        have bodyExtended := jumpExtended.of_adv (adv_emitTerm jumpRun)
        have startExtended := bodyExtended.of_adv (advB_lowerBlock _ [] false body _ _ _ _ bodyRun)
        rw [bodyEq] at startExtended
        exact startExtended
      have post := generated_while_reentry_post branch headerInput.atPoint headerInput.related boundary.post
        forkRun forkExtended bodyEq bodyRun ended
      obtain ⟨next, typing, roots, world, observation, plans, path, context, input, bounded, realized, back⟩ :=
        accepted_generated_while_reentry source branch canonicalBranch evaluated bodyDone headerInput headerTarget headerBounded
          bodyRun jumpRun jumpExtended ended (outerPost := by cases loop <;> simp_all)
      obtain ⟨nextOwned, nextAdmitted, nextOccurrence, nextRows⟩ :=
        generated_while_reentry_context source next roots plans path context selected owned occurrence rows admitted
      have iteration := WhileIterations.next evaluated bodyDone (Or.inl ⟨.unit, rfl⟩) (WhileIterations.zero current.state)
      have allIterations : WhileIterations cfg env condition body (count + 1) initialState current.state := by
        simpa using iterations.append iteration
      rcases suffix.uncons with ⟨zero, rfl⟩ | ⟨tail, nextPoint, tailCount, last, afterBack⟩
      · exact (stopped.excludes_step_nonTimeout nonTimeout (back targetFuel)).elim
      · obtain ⟨lastFuel, actualBack⟩ := runtimeStep_demandInstructionStep last
        have backEqual := actualBack.deterministic (back lastFuel)
        have nextEq : nextPoint = ⟨(header, 0), current.frame, current.state⟩ := by cases nextPoint; exact backEqual
        subst nextPoint
        exact Or.inr ⟨consumed + 2, tail, ⟨(header, 0), current.frame, current.state⟩, next, allIterations, by omega, by omega,
          by simpa [Nat.add_assoc] using (DemandRuntimePrefix.next first executed).append (.next last (.zero _)),
          afterBack, typing, roots, world, observation, plans, path, context, input, post, bounded, realized, rfl,
          nextOwned, nextAdmitted, nextOccurrence, nextRows⟩


theorem accepted_generated_while_scalar_call_true_stopped {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state middle initialState : St} {count : Nat}
    (iterations : WhileIterations cfg env condition body count initialState state) (source : StmtSource cfg env (.while condition body origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    {fuel : Nat} (evaluated : evalExpr fuel cfg env condition state = .ok (.bool true) middle)
    (fragment : ReachableScalarCallStatements cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } body.stmts)
    (noValue : body.value = none)
    {cx : FnCtx} {results : List Ty} {loop : Option LoopCtx} {root : DemandNode} {owner : Nat}
    (targetConfig : cx.cfg = ⟨cfg.profile, lower cfg.mod⟩)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context) {before headerState built : LS}
    {header : BlockId} {initial frame : GIR.Frame} {point : Pt}
    (headerInput : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv headerState initial (header, 0))
    (headerTarget : ∃ block, cx.fn.blocks[header]? = some block ∧ block.params = [])
    (headerId : header = (newBlock [] (lowerEnv cfg.mod env.vars results) before).1.1)
    (headerEq : headerState = demandWhileHeaderBefore (lowerEnv cfg.mod env.vars results) before)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.while condition body origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (headerBounded : map.Bounded headerState.vals.size)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (boundary : ExpressionDemandBoundary child map cx headerState initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1 (.bool true) middle point frame)
    (conditionReach : Evidence.RuntimePoint cx.cfg cx.fn point frame middle)
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) headerState = ((), built)) (extended : ExtT built cx.fn.blocks)

    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨point, frame, middle⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    (∃ sourceFuel, execStmt sourceFuel cfg env (.while condition body origin) initialState = .stop stop after) ∨
    ∃ (consumed remaining : Nat) (current : DemandRuntimePoint)
      (next : StmtSource cfg env (.while condition body origin) current.state),
      WhileIterations cfg env condition body (count + 1) initialState current.state ∧
      consumed + remaining = taken ∧ 0 < consumed ∧ DemandRuntimePrefix cx consumed ⟨point, frame, middle⟩ current ∧
      DemandRuntimePrefix cx remaining current reached ∧
      next.typingEnv = source.typingEnv ∧ next.rootsEnv = source.rootsEnv ∧ next.world = source.world ∧
      next.observation = source.observation ∧ next.plans = source.plans ∧ next.path = source.path ∧ HEq next.context source.context ∧
      GeneratedPrefixInput cfg env cx results loop next.typingEnv next.rootsEnv headerState current.frame (header, 0) ∧
      Post cfg env cx headerState initial headerState current.frame (header, 0) [] ∧
      map.Bounded headerState.vals.size ∧ map.Realizes cfg.mod next.world env ⟨(header, 0), current.frame, current.state⟩ ∧
      current.point = (header, 0) ∧ GeneratedSourceOwner selected next.context ∧
      map.Admitted cfg.mod.profile next.context.retained ∧
      ∃ nextOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root next.path (.statement loop (.while condition body origin)) before,
        GeneratedDemandRows cfg.mod next.rootsEnv.access nextOccurrence required := by
  have bounded : BoundedNestedCallLoopStatements cfg 0
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } body.stmts := .mixed fragment
  have families : ∀ (before : LS) (innerLoop : Option LoopCtx),
      ReachableSequencePrefixFamily (env := { env with scopes := (body.scope, middle.nextScope) :: env.scopes }) cx results selected before innerLoop [] false body body.stmts
        (@NestedCallLoopCursor cfg cx.fn results root owner 0 { env with scopes := (body.scope, middle.nextScope) :: env.scopes } innerLoop selected) ∧
      ReachableStoppedSequencePrefixFamily (env := { env with scopes := (body.scope, middle.nextScope) :: env.scopes }) cx results selected before innerLoop [] false body body.stmts := by
    intro before innerLoop
    cases cx with
    | mk current caller =>
      change current = ⟨cfg.profile, lower cfg.mod⟩ at targetConfig
      subst current
      exact accepted_generated_reachable_scalar_call_statements fragment selected before innerLoop [] false body
  exact accepted_generated_while_bounded_nested_call_true_stopped iterations source child canonical evaluated bounded noValue
    targetConfig selected families owned headerInput headerTarget headerId headerEq occurrence rows headerBounded coverage admitted boundary
    conditionReach lowered extended steps stopped nonTimeout

#print axioms accepted_generated_while_scalar_call_true_stopped
#print axioms accepted_generated_while_bounded_nested_call_true_stopped
end Goose.Lower

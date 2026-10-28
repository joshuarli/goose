import Goose.Lower.DemandScalarAssignmentStatementAgreement

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_if_condition_extended {le : LEnv} {before : LS} {loop : Option LoopCtx}
    {condition : Expr} {yes : Core.Block} {no : Option Core.Block} {origin : OriginId} {blocks : Array GIR.Block}
    (extended : ExtT (lowerStmt loop (.ifS condition yes no origin) le before).2 blocks) :
    ExtT (lowerExpr condition le before).2 blocks := by
  let lowered := lowerExpr condition le before
  cases no with
  | none =>
    have advance := advB_ifS_none_core lowered.1 (advB_lowerBlock loop [] false yes) le lowered.2 _ _ rfl
    apply extended.of_adv
    simpa only [lowerStmt, bind_run, lowered, whenLive, curBlock_run] using advance
  | some no =>
    have advance := advB_ifS_some_core lowered.1 (advB_lowerBlock loop [] false yes) (advB_lowerBlock loop [] false no)
      le lowered.2 _ _ rfl
    apply extended.of_adv
    simpa only [lowerStmt, bind_run, lowered, whenLive, curBlock_run] using advance

theorem accepted_generated_if_condition_prefix {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat} {loop : Option LoopCtx} {condition : Expr} {yes : Core.Block} {no : Option Core.Block}
    {origin : OriginId} {state : St} (source : StmtSource cfg env (.ifS condition yes no origin) state)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context) {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.ifS condition yes no origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerStmt loop (.ifS condition yes no origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (family : GeneratedExpressionPrefixFamily cx results selected loop condition (@CanonicalExpressionPrefixCursor cfg env cx))
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    ∃ child : ExprSource cfg env condition state,
      child.ty = .bool ∧ source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]) ∧
      DemandPrefixDecomposition cx (fun fuel => evalExpr fuel cfg env condition) (CanonicalExpressionDemand map cx child)
        (GeneratedExpressionPrefixEnd child map cx before initial
          (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
          (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1)
        taken ⟨start, initial, state⟩ reached := by
  obtain ⟨child, typing, roots, ty, canonical⟩ := source.ifConditionChildAt
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root child.path (.expression condition) before := by
    rw [canonical.path]
    exact .first occurrence (.ifCondition loop condition yes no origin)
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access
        (.first occurrence (.ifCondition loop condition yes no origin)) required := .first (first := .ifCondition loop condition yes no origin) rows
    simpa only [roots, canonical.path] using inherited
  have childOwner : GeneratedSourceOwner selected child.context :=
    (owned.child rfl 0 (.expression condition) .expression (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).transport
      canonical.plans.symm canonical.path.symm rfl canonical.context.symm
  have childAdmitted : map.Admitted cfg.mod.profile child.context.retained := by
    rw [demandContextRetainedEq canonical.plans canonical.path rfl canonical.context]
    intro profile alias member
    exact source.context.child_retained_subset rfl 0 (.expression condition) .expression
      (by simp [DemandNode.child?, DemandNode.children]) (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
      (admitted profile alias member)
  have childRealized : map.Realizes cfg.mod child.world env ⟨start, initial, state⟩ := by
    simpa only [canonical.world] using realized
  have childInput : GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv before initial start := by
    simpa only [typing, roots] using input
  have progress := family child childOwner childOccurrence childRows coverage childAdmitted bounded childRealized childInput
    (generated_if_condition_extended extended) steps
  exact ⟨child, ty, canonical, progress.progress⟩

theorem accepted_generated_if_condition_stopped {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat} {loop : Option LoopCtx} {condition : Expr} {yes : Core.Block} {no : Option Core.Block}
    {origin : OriginId} {state : St} (source : StmtSource cfg env (.ifS condition yes no origin) state)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context) {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.ifS condition yes no origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerStmt loop (.ifS condition yes no origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (family : GeneratedStoppedExpressionPrefixFamily cx results selected loop condition)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St} (stopped : DemandInstructionStop cx targetFuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    ∃ child : ExprSource cfg env condition state,
      child.ty = .bool ∧ source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]) ∧
      StoppedExpressionPrefix child map cx results before initial start taken reached stop after := by
  obtain ⟨child, typing, roots, ty, canonical⟩ := source.ifConditionChildAt
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root child.path (.expression condition) before := by
    rw [canonical.path]
    exact .first occurrence (.ifCondition loop condition yes no origin)
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access
        (.first occurrence (.ifCondition loop condition yes no origin)) required := .first (first := .ifCondition loop condition yes no origin) rows
    simpa only [roots, canonical.path] using inherited
  have childOwner : GeneratedSourceOwner selected child.context :=
    (owned.child rfl 0 (.expression condition) .expression (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).transport
      canonical.plans.symm canonical.path.symm rfl canonical.context.symm
  have childAdmitted : map.Admitted cfg.mod.profile child.context.retained := by
    rw [demandContextRetainedEq canonical.plans canonical.path rfl canonical.context]
    intro profile alias member
    exact source.context.child_retained_subset rfl 0 (.expression condition) .expression
      (by simp [DemandNode.child?, DemandNode.children]) (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
      (admitted profile alias member)
  have childRealized : map.Realizes cfg.mod child.world env ⟨start, initial, state⟩ := by
    simpa only [canonical.world] using realized
  have childInput : GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv before initial start := by
    simpa only [typing, roots] using input
  have progress := family child childOwner childOccurrence childRows coverage childAdmitted bounded childRealized childInput
    (generated_if_condition_extended extended) steps stopped nonTimeout
  exact ⟨child, ty, canonical, progress⟩


theorem if_condition_stop {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block} {no : Option Core.Block}
    {origin : OriginId} {state after : St} {fuel : Nat} {stop : Stop}
    (stopped : evalExpr fuel cfg env condition state = .stop stop after) :
    execStmt (fuel + 1) cfg env (.ifS condition yes no origin) state = .stop stop after := by
  simp only [execStmt, bind_apply, stopped]

inductive AcceptedIfSelection {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block}
    {no : Option Core.Block} {origin : OriginId} {state after : St}
    (source : StmtSource cfg env (.ifS condition yes no origin) state) (fuel : Nat) : Val → Prop
  | yes (evaluated : evalExpr fuel cfg env condition state = .ok (.bool true) after)
      (child : BlockSource cfg env [] yes after) (typing : child.typingEnv = source.typingEnv)
      (roots : child.rootsEnv = source.rootsEnv) (world : child.world = source.world)
      (observation : child.observation = source.observation)
      (canonical : source.BlockChildAt child 1 (by simp [DemandNode.child?, DemandNode.children])) :
      AcceptedIfSelection source fuel (.bool true)
  | no {block : Core.Block} (branch : no = some block)
      (evaluated : evalExpr fuel cfg env condition state = .ok (.bool false) after)
      (child : BlockSource cfg env [] block after) (typing : child.typingEnv = source.typingEnv)
      (roots : child.rootsEnv = source.rootsEnv) (world : child.world = source.world)
      (observation : child.observation = source.observation)
      (canonical : source.BlockChildAt child 2 (by simp [DemandNode.child?, DemandNode.children, branch])) :
      AcceptedIfSelection source fuel (.bool false)
  | skip (branch : no = none) (evaluated : evalExpr fuel cfg env condition state = .ok (.bool false) after) :
      AcceptedIfSelection source fuel (.bool false)

theorem accepted_if_selection {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block}
    {no : Option Core.Block} {origin : OriginId} {state after : St}
    (source : StmtSource cfg env (.ifS condition yes no origin) state) {fuel : Nat} {value : Val}
    (evaluated : evalExpr fuel cfg env condition state = .ok value after) :
    AcceptedIfSelection (after := after) source fuel value := by
  obtain ⟨child, _, _, ty, _⟩ := source.ifConditionChildAt
  have result := child.result fuel value evaluated
  have typed := result.typed
  rw [ty] at typed
  obtain ⟨boolean, rfl⟩ := hasTy_bool typed
  cases boolean with
  | true =>
    obtain ⟨body, typing, roots, world, observation, canonical⟩ := source.ifThenChildAt fuel evaluated
    exact .yes evaluated body typing roots world observation canonical
  | false =>
    cases no with
    | none => exact .skip rfl evaluated
    | some block =>
      obtain ⟨body, typing, roots, world, observation, canonical⟩ := source.ifElseChildAt fuel evaluated
      exact .no rfl evaluated body typing roots world observation canonical

theorem accepted_generated_if_condition_selection_prefix {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat} {loop : Option LoopCtx} {condition : Expr} {yes : Core.Block} {no : Option Core.Block}
    {origin : OriginId} {state : St} (source : StmtSource cfg env (.ifS condition yes no origin) state)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context) {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.ifS condition yes no origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerStmt loop (.ifS condition yes no origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (family : GeneratedExpressionPrefixFamily cx results selected loop condition (@CanonicalExpressionPrefixCursor cfg env cx))
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    ∃ child : ExprSource cfg env condition state,
      child.ty = .bool ∧ source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]) ∧
      DemandPrefixDecomposition cx (fun fuel => evalExpr fuel cfg env condition) (CanonicalExpressionDemand map cx child)
        (fun value runtime =>
          GeneratedExpressionPrefixEnd child map cx before initial
            (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
            (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 value runtime ∧
          ∃ fuel, AcceptedIfSelection (after := runtime.state) source fuel value)
        taken ⟨start, initial, state⟩ reached := by
  obtain ⟨child, ty, canonical, progress⟩ := accepted_generated_if_condition_prefix source selected owned occurrence rows
    coverage admitted bounded realized input extended family steps
  refine ⟨child, ty, canonical, ?_⟩
  cases progress with
  | interior demanded => exact .interior demanded
  | complete count prefixSteps residual evaluated post =>
    exact .complete count prefixSteps residual evaluated ⟨post, ⟨_, accepted_if_selection source evaluated⟩⟩

#print axioms accepted_generated_if_condition_selection_prefix
#print axioms StmtSource.ifThenChildAt
#print axioms StmtSource.ifElseChildAt
#print axioms accepted_if_selection
#print axioms if_condition_stop
#print axioms accepted_generated_if_condition_stopped
#print axioms accepted_generated_if_condition_prefix
#print axioms StmtSource.ifConditionChildAt
#print axioms generated_if_condition_extended
end Goose.Lower

import Goose.Lower.DemandWhileCondition

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_while_condition_prefix {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state : St} (source : StmtSource cfg env (.while condition body origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before after : LS}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement none (.while condition body origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {frame : GIR.Frame} {point : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv before frame point)
    (lowered : lowerStmt none (.while condition body origin) (lowerEnv cfg.mod env.vars results) before = ((), after))
    (extended : ExtT after cx.fn.blocks)
    (family : GeneratedExpressionPrefixFamily cx results selected none condition (@CanonicalExpressionPrefixCursor cfg env cx))
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨point, frame, state⟩ reached) :
    (taken = 0 ∧ reached = ⟨point, frame, state⟩) ∨
      ∃ (child : ExprSource cfg env condition state) (header : BlockId) (headerState : LS) (remaining : Nat),
        taken = remaining + 1 ∧ child.ty = .bool ∧
        source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]) ∧
        DemandPrefixDecomposition cx (fun fuel => evalExpr fuel cfg env condition) (CanonicalExpressionDemand map cx child)
          (GeneratedExpressionPrefixEnd child map cx headerState frame
            (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2
            (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1)
          remaining ⟨(header, 0), frame, state⟩ reached := by
  obtain ⟨child, header, headerState, ty, canonical, childOwner, childCoverage, childAdmitted,
    childBounded, childRealized, childInput, childExtended, headerStep, childOccurrence, childRows⟩ :=
    accepted_generated_while_initial_condition source selected owned occurrence rows coverage admitted bounded realized input lowered extended
  rcases steps.uncons with ⟨zero, rfl⟩ | ⟨remaining, next, count, first, suffix⟩
  · exact Or.inl ⟨zero, rfl⟩
  · obtain ⟨fuel, actual⟩ := runtimeStep_demandInstructionStep first
    have equal := actual.deterministic (headerStep fuel)
    have nextEq : next = ⟨(header, 0), frame, state⟩ := by cases next; exact equal
    subst next
    have progress := family child childOwner childOccurrence childRows childCoverage childAdmitted childBounded
      childRealized childInput childExtended suffix
    exact Or.inr ⟨child, header, headerState, remaining, count, ty, canonical, progress.progress⟩

theorem accepted_generated_while_condition_stopped {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state : St} (source : StmtSource cfg env (.while condition body origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before after : LS}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement none (.while condition body origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {frame : GIR.Frame} {point : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv before frame point)
    (lowered : lowerStmt none (.while condition body origin) (lowerEnv cfg.mod env.vars results) before = ((), after))
    (extended : ExtT after cx.fn.blocks)
    (family : GeneratedStoppedExpressionPrefixFamily cx results selected none condition)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨point, frame, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {final : St} (stopped : DemandInstructionStop cx targetFuel reached stop final)
    (nonTimeout : stop ≠ .timeout) :
    (∃ fuel, execStmt fuel cfg env (.while condition body origin) state = .stop stop final) ∨
      ∃ (child : ExprSource cfg env condition state) (header : BlockId) (headerState : LS) (remaining : Nat),
        taken = remaining + 1 ∧ child.ty = .bool ∧
        source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]) ∧
        StoppedExpressionPrefix child map cx results headerState frame (header, 0) remaining reached stop final := by
  obtain ⟨child, header, headerState, ty, canonical, childOwner, childCoverage, childAdmitted,
    childBounded, childRealized, childInput, childExtended, headerStep, childOccurrence, childRows⟩ :=
    accepted_generated_while_initial_condition source selected owned occurrence rows coverage admitted bounded realized input lowered extended
  rcases steps.uncons with ⟨zero, rfl⟩ | ⟨remaining, next, count, first, suffix⟩
  · exact (stopped.excludes_step_nonTimeout nonTimeout (headerStep targetFuel)).elim
  · obtain ⟨fuel, actual⟩ := runtimeStep_demandInstructionStep first
    have equal := actual.deterministic (headerStep fuel)
    have nextEq : next = ⟨(header, 0), frame, state⟩ := by cases next; exact equal
    subst next
    have progress := family child childOwner childOccurrence childRows childCoverage childAdmitted childBounded
      childRealized childInput childExtended suffix stopped nonTimeout
    cases progress with
    | aborted sourceFuel done =>
      have whileStop := while_condition_stop (body := body) done
      exact Or.inl ⟨sourceFuel + 2, by simp only [execStmt, whileStop]⟩
    | complete count' executed residual evaluated post =>
      exact Or.inr ⟨child, header, headerState, remaining, count, ty, canonical,
        .complete count' executed residual evaluated post⟩

#print axioms accepted_generated_while_condition_stopped
#print axioms accepted_generated_while_condition_prefix
end Goose.Lower

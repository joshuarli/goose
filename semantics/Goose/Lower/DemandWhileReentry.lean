import Goose.Lower.DemandWhileBodyInput
import Goose.Lower.DemandWhileBackEdge

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_while_reentry {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state middle after : St} (source : StmtSource cfg env (.while condition body origin) state)
    (branch : BlockSource cfg env [] body middle)
    (canonical : source.BlockChildAt branch 1 (by simp [DemandNode.child?, DemandNode.children]))
    {conditionFuel bodyFuel : Nat}
    (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool true) middle)
    (bodyDone : execBlock bodyFuel cfg env [] body middle = .ok (.normal .unit) after)
    {cx : FnCtx} {results : List Ty} {headerState bodyStart bodyEnd jumped : LS} {loop : Option LoopCtx}
    {initial conditionFrame finalFrame : GIR.Frame} {header exitBlock bodyValue : Nat} {bodyPoint : Pt}
    {map required : RetainedSsaMap}
    (headerInput : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv headerState initial (header, 0))
    (headerTarget : ∃ block, cx.fn.blocks[header]? = some block ∧ block.params = [])
    (bounded : map.Bounded headerState.vals.size)
    (bodyRun : lowerBlock (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length,
      exitBlock, .jump header⟩) [] false body (lowerEnv cfg.mod env.vars results) bodyStart = (bodyValue, bodyEnd))
    (jumpRun : emitTerm (.br header []) (lowerEnv cfg.mod env.vars results) bodyEnd = ((), jumped))
    (jumpExtended : ExtT jumped cx.fn.blocks)
    (ended : GeneratedBranchBlockEnd branch map required cx results bodyStart
      (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
      conditionFrame (.normal .unit) ⟨bodyPoint, finalFrame, after⟩)
    (outerPost : match loop with | none => True | some _ => Post cfg env cx headerState initial headerState finalFrame (header, 0) [] := by trivial) :
    ∃ next : StmtSource cfg env (.while condition body origin) after,
      next.typingEnv = source.typingEnv ∧ next.rootsEnv = source.rootsEnv ∧ next.world = source.world ∧
      next.observation = source.observation ∧ next.plans = source.plans ∧ next.path = source.path ∧ HEq next.context source.context ∧
      GeneratedPrefixInput cfg env cx results loop next.typingEnv next.rootsEnv headerState finalFrame (header, 0) ∧
      map.Bounded headerState.vals.size ∧ map.Realizes cfg.mod next.world env ⟨(header, 0), finalFrame, after⟩ ∧
      ∀ fuel, DemandInstructionStep cx fuel ⟨bodyPoint, finalFrame, after⟩ ⟨(header, 0), finalFrame, after⟩ := by
  obtain ⟨next, typing, roots, world, observation, plans, path, context⟩ :=
    source.whileAfterBodyCanonical conditionFuel bodyFuel (.normal .unit) conditionDone bodyDone (Or.inl ⟨.unit, rfl⟩)
  have bodyPost : Post cfg env cx bodyStart conditionFrame bodyEnd finalFrame bodyPoint [] := by
    simpa only [bodyRun] using ended.post
  have related : Rel cfg env cx finalFrame headerState := bodyPost.rel.stack_eq (by
    rw [headerInput.related.stack, bodyPost.rel.stack])
  have nextInput : GeneratedPrefixInput cfg env cx results loop next.typingEnv next.rootsEnv headerState finalFrame (header, 0) := by
    have nextMetadata : SourceResults next.typingEnv next.rootsEnv results := by
      simpa only [typing, roots] using headerInput.metadata
    have nextLoops : LoopSourceMatches next.typingEnv loop := by
      simpa only [typing] using headerInput.loops
    cases loop with
    | none => exact ⟨nextMetadata, nextLoops, headerInput.atPoint, related, headerInput.moduleEq, headerInput.resultsEq,
        headerInput.depth, trivial, trivial, headerInput.generated, trivial⟩
    | some context => exact ⟨nextMetadata, nextLoops, headerInput.atPoint, related, headerInput.moduleEq, headerInput.resultsEq,
        headerInput.depth, headerInput.targets, headerInput.counter.afterPost outerPost, headerInput.generated, headerInput.frames⟩
  have realized : map.Realizes cfg.mod next.world env ⟨(header, 0), finalFrame, after⟩ := by
    simpa only [RetainedSsaMap.Realizes, world, canonical.world] using ended.demanded.operands
  exact ⟨next, typing, roots, world, observation, plans, path, context, nextInput, bounded, realized,
    generated_while_back_edge jumpRun bodyPost.pp jumpExtended headerTarget⟩

#print axioms accepted_generated_while_reentry
end Goose.Lower

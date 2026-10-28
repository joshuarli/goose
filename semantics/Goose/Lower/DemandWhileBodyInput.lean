import Goose.Lower.DemandWhileBodyEntry

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_while_body_input {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state middle : St}
    (source : StmtSource cfg env (.while condition body origin) state)
    (child : ExprSource cfg env condition state) (branch : BlockSource cfg env [] body middle)
    (typing : branch.typingEnv = { source.typingEnv with loops := source.typingEnv.loops + 1 })
    (roots : branch.rootsEnv = source.rootsEnv)
    {cx : FnCtx} {results : List Ty} {loop : Option LoopCtx} {headerState forked bodyStart : LS}
    {initial frame : GIR.Frame} {header : BlockId} {point : Pt} {map : RetainedSsaMap}
    {bodyBlock exitBlock : BlockId}
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv headerState initial (header, 0))
    (headerTarget : ∃ block, cx.fn.blocks[header]? = some block ∧ block.params = [])
    (boundary : ExpressionDemandBoundary child map cx headerState initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1 (.bool true) middle point frame)
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2 =
      ((bodyBlock, exitBlock), forked))
    (bodyEq : bodyStart = { forked with cur := some bodyBlock }) (extended : ExtT forked cx.fn.blocks) :
    GeneratedPrefixInput cfg env cx results
      (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
      branch.typingEnv branch.rootsEnv bodyStart frame (bodyBlock, 0) := by
  let le := lowerEnv cfg.mod env.vars results
  let first := lowerExpr condition le headerState
  let context : LoopCtx := ⟨first.2.stack.length, exitBlock, .jump header⟩
  obtain ⟨_, _, _, _, stackEq, _, _, bodyAt, exitAt⟩ := fork_facts forkRun boundary.post.pp extended
  have conditionAdvance := advB_lowerExpr condition le headerState first.1 first.2 rfl
  have forkAdvance := advB_fork first.1 le first.2 _ forked forkRun
  have conditionExtended : ExtT first.2 cx.fn.blocks := extended.of_adv forkAdvance
  have headerExtended : ExtT headerState cx.fn.blocks := conditionExtended.of_adv conditionAdvance
  obtain ⟨localHeader, _, localAt, _⟩ := LS.pp_some input.atPoint
  obtain ⟨finalHeader, finalAt, finalParams⟩ := headerExtended.params localAt
  obtain ⟨targetHeader, targetAt, targetParams⟩ := headerTarget
  have same : finalHeader = targetHeader := Option.some.inj (finalAt.symm.trans targetAt)
  have localParams : localHeader.params = [] := by rw [← finalParams, same]; exact targetParams
  have headerFrames : LoopBuilderFrames (some ⟨first.2.stack.length, header, .jump header⟩) headerState :=
    ⟨⟨localHeader, localAt, localParams⟩, ⟨localHeader, localAt, localParams⟩⟩
  have forkFrames := (headerFrames.mono conditionAdvance.ext).mono forkAdvance.ext
  have carried := forkFrames.of_blocks (show bodyStart.blocks = forked.blocks by rw [bodyEq])
  have bodyFrames : LoopBuilderFrames (some context) bodyStart := by
    refine ⟨⟨⟨[], #[]⟩, ?_, rfl⟩, carried.2⟩
    rw [bodyEq]
    exact exitAt
  have forkGenerated := (input.generated.lowerExpr condition rfl).fork first.1 forkRun
  have bodyGenerated : GeneratedBuilderState bodyStart := by
    rw [bodyEq]
    exact forkGenerated.setCur (env := le) (some bodyBlock)
      (by intro current same; cases same; exact (Array.getElem?_eq_some_iff.mp bodyAt).1) rfl
  have bodyPoint : bodyStart.pp = some (bodyBlock, 0) := by rw [bodyEq]; exact LS.pp_cur bodyAt
  have bodyRelated : Rel cfg env cx frame bodyStart := by
    apply boundary.post.rel.stack_eq
    rw [bodyEq]
    exact stackEq
  obtain ⟨exitTarget, exitTargetAt, exitParams⟩ := extended.params exitAt
  have targets : LoopTargets cx.fn context := ⟨⟨exitTarget, exitTargetAt, exitParams⟩, ⟨targetHeader, targetAt, targetParams⟩⟩
  have depth : LoopDepthFits env (some context) := by
    change first.2.stack.length ≤ env.scopes.length
    rw [boundary.post.rel.stack]
    simp
  refine ⟨?_, ?_, bodyPoint, bodyRelated, input.moduleEq, input.resultsEq, depth, targets, trivial, bodyGenerated, bodyFrames⟩
  · apply input.metadata.transport
    · rw [typing]
    · rw [roots]
  · rw [typing]
    simp [LoopSourceMatches]

#print axioms generated_while_body_input
end Goose.Lower

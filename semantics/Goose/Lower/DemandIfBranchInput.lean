import Goose.Lower.DemandIfLowering
import Goose.Lower.DemandGeneratedShortCircuitPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_if_branch_input {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block}
    {no : Option Core.Block} {origin : OriginId} {state middle : St}
    (source : StmtSource cfg env (.ifS condition yes no origin) state)
    (child : ExprSource cfg env condition state) (branch : BlockSource cfg env [] yes middle)
    (typing : branch.typingEnv = source.typingEnv) (roots : branch.rootsEnv = source.rootsEnv)
    {cx : FnCtx} {results : List Ty} {before forked branchStart : LS}
    {initial frame : GIR.Frame} {start point : Pt} {map : RetainedSsaMap} {loop : Option LoopCtx}
    {yesBlock noBlock : BlockId} (value : Bool)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (boundary : ExpressionDemandBoundary child map cx before initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (.bool value) middle point frame)
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 =
      ((yesBlock, noBlock), forked))
    (startEq : branchStart = { forked with cur := some yesBlock })
    (extended : ExtT forked cx.fn.blocks) :
    GeneratedPrefixInput cfg env cx results loop branch.typingEnv branch.rootsEnv branchStart frame (yesBlock, 0) := by
  let le := lowerEnv cfg.mod env.vars results
  let first := lowerExpr condition le before
  obtain ⟨_, _, _, valsEq, stackEq, _, _, yesAt, _⟩ := fork_facts forkRun boundary.post.pp extended
  have firstAdv := advB_lowerExpr condition le before first.1 first.2 rfl
  have forkAdv := advB_fork first.1 le first.2 _ forked forkRun
  have firstGenerated : GeneratedBuilderState first.2 := input.generated.lowerExpr condition rfl
  have forkGenerated : GeneratedBuilderState forked := firstGenerated.fork first.1 forkRun
  have branchGenerated : GeneratedBuilderState branchStart := by
    rw [startEq]
    exact forkGenerated.setCur (env := le) (some yesBlock)
      (by intro current same; cases same; exact (Array.getElem?_eq_some_iff.mp yesAt).1) rfl
  have firstFrames : LoopBuilderFrames loop first.2 := input.frames.mono firstAdv.ext
  have forkFrames : LoopBuilderFrames loop forked := firstFrames.mono forkAdv.ext
  have branchFrames : LoopBuilderFrames loop branchStart := by rw [startEq]; exact forkFrames.of_blocks rfl
  have firstCounter : LoopCounterAt loop first.2 frame := input.counter.afterPost (boundary.post.sub (by simp))
  have branchCounter : LoopCounterAt loop branchStart frame := by
    cases loop with
    | none => trivial
    | some context =>
      cases kind : context.cont with
      | jump header => simp [LoopCounterAt, kind]
      | next header type counter =>
        simp only [LoopCounterAt, kind] at firstCounter ⊢
        obtain ⟨bound, witness⟩ := firstCounter
        refine ⟨?_, witness⟩
        rw [startEq]
        change counter < forked.vals.size
        rw [valsEq]
        exact bound
  have branchPoint : branchStart.pp = some (yesBlock, 0) := by rw [startEq]; exact LS.pp_cur yesAt
  have branchRel : Rel cfg env cx frame branchStart := by
    apply boundary.post.rel.stack_eq
    rw [startEq]
    exact stackEq
  refine ⟨?_, ?_, branchPoint, branchRel, input.moduleEq, input.resultsEq,
    input.depth, ?_, branchCounter, branchGenerated, branchFrames⟩
  · simpa only [typing, roots] using input.metadata
  · simpa only [typing] using input.loops
  · cases loop <;> exact input.targets

theorem accepted_generated_if_then_input {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block}
    {no : Option Core.Block} {origin : OriginId} {state middle : St}
    (source : StmtSource cfg env (.ifS condition yes no origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    {sourceFuel : Nat} (evaluated : evalExpr sourceFuel cfg env condition state = .ok (.bool true) middle)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    {before forked branchStart : LS} {initial frame : GIR.Frame} {start point : Pt}
    {map : RetainedSsaMap} {loop : Option LoopCtx} {yesBlock noBlock : BlockId}
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (boundary : ExpressionDemandBoundary child map cx before initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (.bool true) middle point frame)
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 =
      ((yesBlock, noBlock), forked))
    (startEq : branchStart = { forked with cur := some yesBlock })
    (extended : ExtT forked cx.fn.blocks) :
    ∃ branch : BlockSource cfg env [] yes middle,
      branch.typingEnv = source.typingEnv ∧ branch.rootsEnv = source.rootsEnv ∧
      source.BlockChildAt branch 1 (by simp [DemandNode.child?, DemandNode.children]) ∧
      GeneratedSourceOwner selected branch.context ∧ map.Admitted cfg.mod.profile branch.context.retained ∧
      map.Bounded branchStart.vals.size ∧ map.Realizes cfg.mod branch.world env ⟨(yesBlock, 0), frame, middle⟩ ∧
      GeneratedPrefixInput cfg env cx results loop branch.typingEnv branch.rootsEnv branchStart frame (yesBlock, 0) := by
  obtain ⟨branch, typing, roots, world, _, branchCanonical⟩ := source.ifThenChildAt sourceFuel evaluated
  have branchOwner : GeneratedSourceOwner selected branch.context :=
    (owned.child rfl 1 (.block yes) .block (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).transport
      branchCanonical.plans.symm branchCanonical.path.symm rfl branchCanonical.context.symm
  have branchAdmitted : map.Admitted cfg.mod.profile branch.context.retained := by
    rw [demandContextRetainedEq branchCanonical.plans branchCanonical.path rfl branchCanonical.context]
    intro profile alias member
    exact source.context.child_retained_subset rfl 1 (.block yes) .block
      (by simp [DemandNode.child?, DemandNode.children]) (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
      (admitted profile alias member)
  obtain ⟨_, _, _, valsEq, _, _, _, _, _⟩ := fork_facts forkRun boundary.post.pp extended
  have branchBounded : map.Bounded branchStart.vals.size := by
    rw [startEq]
    change map.Bounded forked.vals.size
    rw [valsEq]
    exact boundary.bounded
  have branchRealized : map.Realizes cfg.mod branch.world env ⟨(yesBlock, 0), frame, middle⟩ := by
    simpa only [RetainedSsaMap.Realizes, world, canonical.world] using boundary.demanded.operands
  exact ⟨branch, typing, roots, branchCanonical, branchOwner, branchAdmitted, branchBounded, branchRealized,
    generated_if_branch_input source child branch typing roots true input boundary forkRun startEq extended⟩

#print axioms accepted_generated_if_then_input
#print axioms generated_if_branch_input
end Goose.Lower

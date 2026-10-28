import Goose.Lower.DemandIfElseOccurrence

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_if_else_input {cfg : Cfg} {env : Env} {condition : Expr} {yes no : Core.Block}
    {origin : OriginId} {state middle : St}
    (source : StmtSource cfg env (.ifS condition yes (some no) origin) state)
    (child : ExprSource cfg env condition state) (branch : BlockSource cfg env [] no middle)
    (typing : branch.typingEnv = source.typingEnv) (roots : branch.rootsEnv = source.rootsEnv)
    {cx : FnCtx} {results : List Ty} {before forked yesStart yesEnd noStart : LS}
    {initial frame : GIR.Frame} {start point : Pt} {map : RetainedSsaMap} {loop : Option LoopCtx}
    {yesBlock noBlock value : Nat}
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (boundary : ExpressionDemandBoundary child map cx before initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (.bool false) middle point frame)
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 =
      ((yesBlock, noBlock), forked))
    (yesStartEq : yesStart = { forked with cur := some yesBlock })
    (yesRun : lowerBlock loop [] false yes (lowerEnv cfg.mod env.vars results) yesStart = (value, yesEnd))
    (noStartEq : noStart = { yesEnd with cur := some noBlock })
    (extended : ExtT forked cx.fn.blocks) :
    GeneratedPrefixInput cfg env cx results loop branch.typingEnv branch.rootsEnv noStart frame (noBlock, 0) := by
  let le := lowerEnv cfg.mod env.vars results
  let first := lowerExpr condition le before
  obtain ⟨yesId, noId, _, valsEq, stackEq, _, _, yesAt, noAt⟩ := fork_facts forkRun boundary.post.pp extended
  have firstAdv := advB_lowerExpr condition le before first.1 first.2 rfl
  have forkAdv := advB_fork first.1 le first.2 _ forked forkRun
  have yesAdv := advB_lowerBlock loop [] false yes _ _ _ _ yesRun
  have noAtEnd : yesEnd.blocks[noBlock]? = some ⟨[], #[]⟩ := by
    apply yesAdv.keep noBlock ⟨[], #[]⟩
    · rw [yesStartEq]
      intro equal
      have same := Option.some.inj equal
      nat_omega
    · rw [yesStartEq]
      exact noAt
  have firstGenerated : GeneratedBuilderState first.2 := input.generated.lowerExpr condition rfl
  have forkGenerated : GeneratedBuilderState forked := firstGenerated.fork first.1 forkRun
  have yesGenerated : GeneratedBuilderState yesStart := by
    rw [yesStartEq]
    exact forkGenerated.setCur (env := le) (some yesBlock)
      (by intro current same; cases same; exact (Array.getElem?_eq_some_iff.mp yesAt).1) rfl
  have firstFrames : LoopBuilderFrames loop first.2 := input.frames.mono firstAdv.ext
  have forkFrames : LoopBuilderFrames loop forked := firstFrames.mono forkAdv.ext
  have yesFrames : LoopBuilderFrames loop yesStart := by rw [yesStartEq]; exact forkFrames.of_blocks rfl
  have yesEndGenerated : GeneratedBuilderState yesEnd := yesGenerated.lowerBlock loop [] false yes yesFrames.toTargets yesRun
  have noGenerated : GeneratedBuilderState noStart := by
    rw [noStartEq]
    exact yesEndGenerated.setCur (env := le) (some noBlock)
      (by intro current same; cases same; exact (Array.getElem?_eq_some_iff.mp noAtEnd).1) rfl
  have endFrames : LoopBuilderFrames loop yesEnd := yesFrames.mono yesAdv.ext
  have noFrames : LoopBuilderFrames loop noStart := by rw [noStartEq]; exact endFrames.of_blocks rfl
  have firstCounter : LoopCounterAt loop first.2 frame := input.counter.afterPost (boundary.post.sub (by simp))
  have noCounter : LoopCounterAt loop noStart frame := by
    cases loop with
    | none => trivial
    | some context =>
      cases kind : context.cont with
      | jump header => simp [LoopCounterAt, kind]
      | next header type counter =>
        simp only [LoopCounterAt, kind] at firstCounter ⊢
        obtain ⟨bound, witness⟩ := firstCounter
        refine ⟨?_, witness⟩
        rw [noStartEq]
        change counter < yesEnd.vals.size
        have size := yesAdv.vals
        rw [yesStartEq] at size
        change forked.vals.size ≤ yesEnd.vals.size at size
        rw [valsEq] at size
        exact Nat.lt_of_lt_of_le bound size
  have noPoint : noStart.pp = some (noBlock, 0) := by rw [noStartEq]; exact LS.pp_cur noAtEnd
  have noRel : Rel cfg env cx frame noStart := by
    apply boundary.post.rel.stack_eq
    rw [noStartEq]
    change yesEnd.stack = first.2.stack
    rw [yesAdv.stack, yesStartEq]
    exact stackEq
  refine ⟨?_, ?_, noPoint, noRel, input.moduleEq, input.resultsEq,
    input.depth, ?_, noCounter, noGenerated, noFrames⟩
  · simpa only [typing, roots] using input.metadata
  · simpa only [typing] using input.loops
  · cases loop <;> exact input.targets

theorem accepted_generated_if_else_input {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block}
    {no : Core.Block} {origin : OriginId} {state middle : St}
    (source : StmtSource cfg env (.ifS condition yes (some no) origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    {sourceFuel : Nat} (evaluated : evalExpr sourceFuel cfg env condition state = .ok (.bool false) middle)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    {before forked yesStart yesEnd branchStart : LS} {initial frame : GIR.Frame} {start point : Pt}
    {map : RetainedSsaMap} {loop : Option LoopCtx} {yesBlock noBlock value : Nat}
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (boundary : ExpressionDemandBoundary child map cx before initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (.bool false) middle point frame)
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 =
      ((yesBlock, noBlock), forked))
    (yesStartEq : yesStart = { forked with cur := some yesBlock })
    (yesRun : lowerBlock loop [] false yes (lowerEnv cfg.mod env.vars results) yesStart = (value, yesEnd))
    (startEq : branchStart = { yesEnd with cur := some noBlock })
    (extended : ExtT forked cx.fn.blocks) :
    ∃ branch : BlockSource cfg env [] no middle,
      branch.typingEnv = source.typingEnv ∧ branch.rootsEnv = source.rootsEnv ∧
      source.BlockChildAt branch 2 (by simp [DemandNode.child?, DemandNode.children]) ∧
      GeneratedSourceOwner selected branch.context ∧ map.Admitted cfg.mod.profile branch.context.retained ∧
      map.Bounded branchStart.vals.size ∧ map.Realizes cfg.mod branch.world env ⟨(noBlock, 0), frame, middle⟩ ∧
      GeneratedPrefixInput cfg env cx results loop branch.typingEnv branch.rootsEnv branchStart frame (noBlock, 0) := by
  obtain ⟨branch, typing, roots, world, _, branchCanonical⟩ := source.ifElseChildAt sourceFuel evaluated
  have branchOwner : GeneratedSourceOwner selected branch.context :=
    (owned.child rfl 2 (.block no) .block (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).transport
      branchCanonical.plans.symm branchCanonical.path.symm rfl branchCanonical.context.symm
  have branchAdmitted : map.Admitted cfg.mod.profile branch.context.retained := by
    rw [demandContextRetainedEq branchCanonical.plans branchCanonical.path rfl branchCanonical.context]
    intro profile alias member
    exact source.context.child_retained_subset rfl 2 (.block no) .block
      (by simp [DemandNode.child?, DemandNode.children]) (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
      (admitted profile alias member)
  obtain ⟨_, _, _, valsEq, _, _, _, _, _⟩ := fork_facts forkRun boundary.post.pp extended
  have yesAdv := advB_lowerBlock loop [] false yes _ _ _ _ yesRun
  have branchBounded : map.Bounded branchStart.vals.size := by
    rw [startEq]
    change map.Bounded yesEnd.vals.size
    apply boundary.bounded.mono
    have size := yesAdv.vals
    rw [yesStartEq] at size
    change forked.vals.size ≤ yesEnd.vals.size at size
    rw [valsEq] at size
    exact size
  have branchRealized : map.Realizes cfg.mod branch.world env ⟨(noBlock, 0), frame, middle⟩ := by
    simpa only [RetainedSsaMap.Realizes, world, canonical.world] using boundary.demanded.operands
  exact ⟨branch, typing, roots, branchCanonical, branchOwner, branchAdmitted, branchBounded, branchRealized,
    generated_if_else_input source child branch typing roots input boundary forkRun yesStartEq yesRun startEq extended⟩


#print axioms accepted_generated_if_else_input
#print axioms generated_if_else_input
end Goose.Lower

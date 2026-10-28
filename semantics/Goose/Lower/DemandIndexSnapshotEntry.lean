import Goose.Lower.DemandIndexAssignmentStop
import Goose.Lower.DemandGeneratedSnapshotStop
import Goose.Lower.DemandGeneratedScalarPrefix
import Goose.Lower.DemandStoppedExpressionFamily

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_index_snapshot_entry {cfg : Cfg} {env : Env} {owner : Place} {index : Expr}
    {origin : OriginId} {state after : St} (source : PlaceSource cfg env (.elem (.of owner) index origin) state)
    (form : ScalarReadPlace owner) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.place (.elem (.of owner) index origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial frame : GIR.Frame} {start point : Pt} {loop : Option LoopCtx}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env owner state = .ok location state)
    (addressPost : Post cfg env cx before initial (lowerPlace owner (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerPlace owner (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    (addressed : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩)
    (extended : ExtT (lowerPlace (.elem (.of owner) index origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Goose.Evidence.RuntimeStep cx.cfg cx.fn point frame state next nextFrame after) :
    ∃ (sample : ViewVal) (aliases : List RetainedAlias) (child : ExprSource cfg env index after),
      evalView (fuel + 1) cfg env (.of owner) state = .ok sample after ∧
      source.ExpressionChildAt child 1 rfl ∧
      source.rootsEnv.access.aliasView (source.path ++ [0]) (.of owner) = .ok aliases ∧
      child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧ (∃ type, child.ty = .int type) ∧
      GeneratedDemandRows cfg.mod source.rootsEnv.access (.index occurrence)
        (required.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases) ∧
      (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).Covers
        (required.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases) ∧
      (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).Admitted
        cfg.mod.profile child.context.retained ∧
      (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).Bounded
        (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.inputFuture
        (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).values
        (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).runs ⟨next, nextFrame, after⟩ ∧
      Post cfg env cx before initial (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 nextFrame next
        [((lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1, .view sample)] ∧
      GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv
        (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 nextFrame next := by
  obtain ⟨_, view, viewTyping, viewRoots, canonical, _⟩ := source.elemChildren origin
  have viewOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root view.path (.view (.of owner)) before := by
    rw [canonical.path]
    exact .first occurrence (.placeView rfl)
  have viewRows : GeneratedDemandRows cfg.mod view.rootsEnv.access viewOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.first occurrence (.placeView rfl)) required :=
      .first (first := .placeView rfl) rows
    simpa only [viewRoots, canonical.path] using inherited
  have viewRealized : map.Realizes cfg.mod view.world env ⟨point, frame, state⟩ := by
    simpa only [canonical.world] using addressed
  have addressBounded : map.Bounded (lowerPlace owner (lowerEnv cfg.mod env.vars results) before).2.vals.size :=
    bounded.mono addressPost.mono
  obtain ⟨sample, _, _, viewed, post, _, _⟩ := accepted_generated_snapshot_runtime_step view viewOccurrence viewRows
    coverage placed addressPost addressBounded viewRealized (generated_index_view_extended extended) step
  obtain ⟨aliases, query⟩ := source.index_scalar_view_alias form
  have entry := accepted_generated_index_entry source occurrence rows coverage admitted bounded realized query viewed post
  obtain ⟨child, childCanonical, childTyping, childRoots, childType, childRows, childCoverage, childAdmitted,
    childBounded, childPoint, childFrame⟩ := entry
  have advance := advB_lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before _ _ rfl
  have childInput : GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv
      (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 nextFrame next := by
    refine ⟨?_, ?_, post.pp, post.rel, input.moduleEq, input.resultsEq, input.depth,
      (by cases loop <;> exact input.targets), input.counter.afterPost (post.sub (by simp)),
      input.generated.lowerView (.of owner) rfl, input.frames.mono advance.ext⟩
    · simpa only [childTyping, childRoots] using input.metadata
    · simpa only [childTyping] using input.loops
  exact ⟨sample, aliases, child, viewed, childCanonical, query, childTyping, childRoots, childType, childRows,
    childCoverage, childAdmitted, childBounded, childFrame, post, childInput⟩

theorem accepted_generated_index_expression_prefix {cfg : Cfg} {env : Env} {owner : Place} {index : Expr}
    {origin : OriginId} {state after : St} (source : PlaceSource cfg env (.elem (.of owner) index origin) state)
    (form : ScalarReadPlace owner) {cx : FnCtx} {results : List Ty} {root : DemandNode} {rootOwner : Nat} {before : LS}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root rootOwner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.place (.elem (.of owner) index origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial frame : GIR.Frame} {start point : Pt} {loop : Option LoopCtx}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env owner state = .ok location state)
    (addressPost : Post cfg env cx before initial (lowerPlace owner (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerPlace owner (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    (addressed : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩)
    (extended : ExtT (lowerPlace (.elem (.of owner) index origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Goose.Evidence.RuntimeStep cx.cfg cx.fn point frame state next nextFrame after)
    (family : GeneratedExpressionPrefixFamily cx results selected loop index (@CanonicalExpressionPrefixCursor cfg env cx))
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨next, nextFrame, after⟩ reached) :
    ∃ (sample : ViewVal) (aliases : List RetainedAlias) (child : ExprSource cfg env index after),
      evalView (fuel + 1) cfg env (.of owner) state = .ok sample after ∧ source.ExpressionChildAt child 1 rfl ∧
      source.rootsEnv.access.aliasView (source.path ++ [0]) (.of owner) = .ok aliases ∧
      Post cfg env cx before initial (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 nextFrame next
        [((lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1, .view sample)] ∧
      DemandPrefixDecomposition cx (fun fuel => evalExpr fuel cfg env index)
        (CanonicalExpressionDemand (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases) cx child)
        (GeneratedExpressionPrefixEnd child (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases)
          cx (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 nextFrame
          (lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).2
          (lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).1)
        taken ⟨next, nextFrame, after⟩ reached := by
  obtain ⟨sample, aliases, child, viewed, canonical, query, typing, roots, childType, inherited, covered, childAdmitted,
    childBounded, childFrame, post, childInput⟩ := accepted_generated_index_snapshot_entry source form occurrence rows
      coverage admitted bounded realized input placed addressPost addressed extended step
  have childOwner : GeneratedSourceOwner selected child.context :=
    (owned.child rfl 1 (.expression index) .expression rfl (by trivial)).transport
      canonical.plans.symm canonical.path.symm rfl canonical.context.symm
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root child.path (.expression index) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 := by
    rw [canonical.path]
    exact .index occurrence
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence
      (required.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases) := by
    simpa only [roots, canonical.path] using inherited
  have childRealized : (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).Realizes
      cfg.mod child.world env ⟨next, nextFrame, after⟩ := childFrame.operands
  have progress := family child childOwner childOccurrence childRows covered childAdmitted childBounded childRealized childInput
    (generated_index_expression_extended extended) steps
  exact ⟨sample, aliases, child, viewed, canonical, query, post, progress.progress⟩

theorem accepted_generated_index_expression_stopped {cfg : Cfg} {env : Env} {owner : Place} {index : Expr}
    {origin : OriginId} {state after : St} (source : PlaceSource cfg env (.elem (.of owner) index origin) state)
    (form : ScalarReadPlace owner) {cx : FnCtx} {results : List Ty} {root : DemandNode} {rootOwner : Nat} {before : LS}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root rootOwner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.place (.elem (.of owner) index origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial frame : GIR.Frame} {start point : Pt} {loop : Option LoopCtx}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env owner state = .ok location state)
    (addressPost : Post cfg env cx before initial (lowerPlace owner (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerPlace owner (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    (addressed : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩)
    (extended : ExtT (lowerPlace (.elem (.of owner) index origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Goose.Evidence.RuntimeStep cx.cfg cx.fn point frame state next nextFrame after)
    (family : GeneratedStoppedExpressionPrefixFamily cx results selected loop index)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨next, nextFrame, after⟩ reached)
    {targetFuel : Nat} {stop : Stop} {final : St} (stopped : DemandInstructionStop cx targetFuel reached stop final)
    (nonTimeout : stop ≠ .timeout) :
    ∃ (sample : ViewVal) (aliases : List RetainedAlias) (child : ExprSource cfg env index after),
      evalView (fuel + 1) cfg env (.of owner) state = .ok sample after ∧ source.ExpressionChildAt child 1 rfl ∧
      source.rootsEnv.access.aliasView (source.path ++ [0]) (.of owner) = .ok aliases ∧
      Post cfg env cx before initial (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 nextFrame next
        [((lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1, .view sample)] ∧
      StoppedExpressionPrefix child (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases)
        cx results (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 nextFrame next taken reached stop final := by
  obtain ⟨sample, aliases, child, viewed, canonical, query, typing, roots, childType, inherited, covered, childAdmitted,
    childBounded, childFrame, post, childInput⟩ := accepted_generated_index_snapshot_entry source form occurrence rows
      coverage admitted bounded realized input placed addressPost addressed extended step
  have childOwner : GeneratedSourceOwner selected child.context :=
    (owned.child rfl 1 (.expression index) .expression rfl (by trivial)).transport
      canonical.plans.symm canonical.path.symm rfl canonical.context.symm
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root child.path (.expression index) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 := by
    rw [canonical.path]
    exact .index occurrence
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence
      (required.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases) := by
    simpa only [roots, canonical.path] using inherited
  have childRealized : (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).Realizes
      cfg.mod child.world env ⟨next, nextFrame, after⟩ := childFrame.operands
  have progress := family child childOwner childOccurrence childRows covered childAdmitted childBounded childRealized childInput
    (generated_index_expression_extended extended) steps stopped nonTimeout
  exact ⟨sample, aliases, child, viewed, canonical, query, post, progress⟩


theorem indexed_assignment_expression_stop {cfg : Cfg} {env : Env} {view : View} {index value : Expr}
    {origin indexOrigin : OriginId} {viewFuel indexFuel : Nat} {state viewed after : St}
    {sample : ViewVal} {stop : Stop} (nonTimeout : stop ≠ .timeout)
    (viewedRun : evalView viewFuel cfg env view state = .ok sample viewed)
    (indexStop : evalExpr indexFuel cfg env index viewed = .stop stop after) :
    execStmt (max viewFuel indexFuel + 2) cfg env (.assign (.elem view index indexOrigin) value origin) state = .stop stop after := by
  let common := max viewFuel indexFuel
  have viewRun : evalView common cfg env view state = .ok sample viewed :=
    ((Goose.Proofs.Fuel.monoAll viewFuel common (by dsimp [common]; exact Nat.le_max_left _ _)).view cfg env view state).1 _ _ viewedRun
  have indexRun : evalExpr common cfg env index viewed = .stop stop after := by
    rcases ((Goose.Proofs.Fuel.monoAll indexFuel common (by dsimp [common]; exact Nat.le_max_right _ _)).expr cfg env index viewed).2 _ _ indexStop with timeout | done
    · cases stop <;> simp_all [Goose.Proofs.Fuel.isTimeout]
    · exact done
  dsimp only [common] at viewRun indexRun
  simp only [execStmt, evalPlace, bind_apply, viewRun, indexRun]

#print axioms indexed_assignment_expression_stop
#print axioms accepted_generated_index_expression_stopped
#print axioms accepted_generated_index_expression_prefix
#print axioms accepted_generated_index_snapshot_entry
end Goose.Lower

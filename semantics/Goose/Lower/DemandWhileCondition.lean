import Goose.Lower.DemandWhileEntry

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_while_condition_entry {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state : St} (source : StmtSource cfg env (.while condition body origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.while condition body origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained) :
    ∃ child : ExprSource cfg env condition state,
      child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧ child.ty = .bool ∧
      source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]) ∧
      GeneratedSourceOwner selected child.context ∧ map.Admitted cfg.mod.profile child.context.retained ∧
      ∃ childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root child.path (.expression condition) (demandWhileHeaderBefore (lowerEnv cfg.mod env.vars results) before),
        GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
  obtain ⟨child, typing, roots, ty, canonical⟩ := source.whileConditionChildAt
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
  have inherited : ∃ childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root (source.path ++ [0]) (.expression condition) (demandWhileHeaderBefore (lowerEnv cfg.mod env.vars results) before),
      GeneratedDemandRows cfg.mod source.rootsEnv.access childOccurrence required :=
    ⟨.whileCondition occurrence, .whileCondition rows⟩
  refine ⟨child, typing, roots, ty, canonical, childOwner, childAdmitted, ?_⟩
  rw [canonical.path, roots]
  exact inherited

theorem generated_while_condition_extended {le : LEnv} {header : BlockId} {before after : LS}
    {condition : Expr} {body : Core.Block} {blocks : Array GIR.Block}
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body) le before = ((), after))
    (extended : ExtT after blocks) : ExtT (lowerExpr condition le before).2 blocks := by
  simp only [lowerWhile, bind_eq] at lowered
  obtain ⟨id, middle, conditionRun, rest⟩ := lowered
  have advance := advB_whenLive () (fun _ =>
    advB_loopBody id (fun _ _ => advB_lowerBlock _ [] false body) (advB_emitTerm _)) le middle () after rest
  have conditionExtended := extended.of_adv advance
  have same : middle = (lowerExpr condition le before).2 := congrArg Prod.snd conditionRun.symm
  rw [← same]
  exact conditionExtended

theorem accepted_generated_while_initial_condition {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state : St} (source : StmtSource cfg env (.while condition body origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before after : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.while condition body origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {frame : GIR.Frame} {point : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before frame point)
    (lowered : lowerStmt loop (.while condition body origin) (lowerEnv cfg.mod env.vars results) before = ((), after))
    (extended : ExtT after cx.fn.blocks) :
    ∃ (child : ExprSource cfg env condition state) (header : BlockId) (headerState : LS),
      child.ty = .bool ∧ source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]) ∧
      GeneratedSourceOwner selected child.context ∧ map.Covers required ∧ map.Admitted cfg.mod.profile child.context.retained ∧
      map.Bounded headerState.vals.size ∧ map.Realizes cfg.mod child.world env ⟨(header, 0), frame, state⟩ ∧
      GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv headerState frame (header, 0) ∧
      ExtT (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2 cx.fn.blocks ∧
      (∀ fuel, DemandInstructionStep cx fuel ⟨point, frame, state⟩ ⟨(header, 0), frame, state⟩) ∧
      ∃ childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root child.path (.expression condition) headerState,
        GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
  obtain ⟨child, typing, roots, ty, canonical, childOwner, childAdmitted, childOccurrence, childRows⟩ :=
    accepted_generated_while_condition_entry source selected owned occurrence rows admitted
  obtain ⟨header, headerState, loopRun, _, headerEq, _, post, generated, step⟩ :=
    generated_while_header_entry lowered input.atPoint extended input.related input.generated
  have childRealized : map.Realizes cfg.mod child.world env ⟨(header, 0), frame, state⟩ := by
    simpa only [RetainedSsaMap.Realizes, canonical.world] using realized
  have headerExtension : before.Ext headerState := by
    rw [headerEq]
    unfold demandWhileHeaderBefore
    exact (advB_newBlock0 (lowerEnv cfg.mod env.vars results) before _ _ rfl).ext.trans (advB_emitTerm _ (lowerEnv cfg.mod env.vars results) _ _ _ rfl).ext
  have childInput : GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv headerState frame (header, 0) := by
    have childMetadata : SourceResults child.typingEnv child.rootsEnv results := by
      simpa only [typing, roots] using input.metadata
    have childLoops : LoopSourceMatches child.typingEnv loop := by
      simpa only [typing] using input.loops
    cases loop with
    | none => exact ⟨childMetadata, childLoops, post.pp, post.rel, input.moduleEq, input.resultsEq,
        input.depth, trivial, trivial, generated, trivial⟩
    | some context => exact ⟨childMetadata, childLoops, post.pp, post.rel, input.moduleEq, input.resultsEq,
        input.depth, input.targets, input.counter.afterPost post, generated, input.frames.mono headerExtension⟩
  refine ⟨child, header, headerState, ty, canonical, childOwner, coverage, childAdmitted,
    bounded.mono post.mono, childRealized, childInput, generated_while_condition_extended loopRun extended, step, ?_⟩
  rw [headerEq]
  exact ⟨childOccurrence, childRows⟩

#print axioms accepted_generated_while_initial_condition
#print axioms generated_while_condition_extended
#print axioms accepted_generated_while_condition_entry
end Goose.Lower

import Goose.Lower.DemandWhileConditionPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_while_header_condition {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state : St} (source : StmtSource cfg env (.while condition body origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before headerState built : LS} {header : BlockId} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.while condition body origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {frame : GIR.Frame} (realized : map.Realizes cfg.mod source.world env ⟨(header, 0), frame, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv headerState frame (header, 0))
    (headerEq : headerState = demandWhileHeaderBefore (lowerEnv cfg.mod env.vars results) before)
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) headerState = ((), built)) (extended : ExtT built cx.fn.blocks) :
    ∃ child : ExprSource cfg env condition state,
      child.ty = .bool ∧ source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]) ∧
      GeneratedSourceOwner selected child.context ∧ map.Admitted cfg.mod.profile child.context.retained ∧
      map.Realizes cfg.mod child.world env ⟨(header, 0), frame, state⟩ ∧
      GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv headerState frame (header, 0) ∧
      ExtT (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2 cx.fn.blocks ∧
      ∃ childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root child.path (.expression condition) headerState,
        GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
  obtain ⟨child, typing, roots, ty, canonical, childOwner, childAdmitted, childOccurrence, childRows⟩ :=
    accepted_generated_while_condition_entry source selected owned occurrence rows admitted
  have childRealized : map.Realizes cfg.mod child.world env ⟨(header, 0), frame, state⟩ := by
    simpa only [RetainedSsaMap.Realizes, canonical.world] using realized
  have childInput : GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv headerState frame (header, 0) := by
    have childMetadata : SourceResults child.typingEnv child.rootsEnv results := by
      simpa only [typing, roots] using input.metadata
    have childLoops : LoopSourceMatches child.typingEnv loop := by
      simpa only [typing] using input.loops
    cases loop with
    | none => exact ⟨childMetadata, childLoops, input.atPoint, input.related, input.moduleEq, input.resultsEq,
        input.depth, trivial, trivial, input.generated, trivial⟩
    | some context => exact ⟨childMetadata, childLoops, input.atPoint, input.related, input.moduleEq, input.resultsEq,
        input.depth, input.targets, input.counter, input.generated, input.frames⟩
  refine ⟨child, ty, canonical, childOwner, childAdmitted, childRealized, childInput,
    generated_while_condition_extended lowered extended, ?_⟩
  rw [headerEq]
  exact ⟨childOccurrence, childRows⟩


theorem accepted_generated_while_header_prefix {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state : St} (source : StmtSource cfg env (.while condition body origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before headerState built : LS} {header : BlockId} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.while condition body origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {frame : GIR.Frame} (realized : map.Realizes cfg.mod source.world env ⟨(header, 0), frame, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv headerState frame (header, 0))
    (headerEq : headerState = demandWhileHeaderBefore (lowerEnv cfg.mod env.vars results) before)
    (coverage : map.Covers required) (bounded : map.Bounded headerState.vals.size)
    (family : GeneratedExpressionPrefixFamily cx results selected loop condition (@CanonicalExpressionPrefixCursor cfg env cx))
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) headerState = ((), built)) (extended : ExtT built cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨(header, 0), frame, state⟩ reached) :
    ∃ child : ExprSource cfg env condition state, child.ty = .bool ∧
      source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]) ∧
      DemandPrefixDecomposition cx (fun fuel => evalExpr fuel cfg env condition) (CanonicalExpressionDemand map cx child)
        (GeneratedExpressionPrefixEnd child map cx headerState frame
          (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2
          (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1)
        taken ⟨(header, 0), frame, state⟩ reached := by
  obtain ⟨child, ty, canonical, childOwner, childAdmitted, childRealized, childInput, childExtended, childOccurrence, childRows⟩ :=
    accepted_generated_while_header_condition source selected owned occurrence rows admitted realized input headerEq lowered extended
  have progress := family child childOwner childOccurrence childRows coverage childAdmitted bounded childRealized childInput childExtended steps
  exact ⟨child, ty, canonical, progress.progress⟩


theorem accepted_generated_while_header_stopped {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state : St} (source : StmtSource cfg env (.while condition body origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before headerState built : LS} {header : BlockId} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.while condition body origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {frame : GIR.Frame} (realized : map.Realizes cfg.mod source.world env ⟨(header, 0), frame, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv headerState frame (header, 0))
    (headerEq : headerState = demandWhileHeaderBefore (lowerEnv cfg.mod env.vars results) before)
    (coverage : map.Covers required) (bounded : map.Bounded headerState.vals.size)
    (family : GeneratedStoppedExpressionPrefixFamily cx results selected loop condition)
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) headerState = ((), built)) (extended : ExtT built cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨(header, 0), frame, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St} (stopped : DemandInstructionStop cx targetFuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    ∃ child : ExprSource cfg env condition state, child.ty = .bool ∧
      source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]) ∧
      StoppedExpressionPrefix child map cx results headerState frame (header, 0) taken reached stop after := by
  obtain ⟨child, ty, canonical, childOwner, childAdmitted, childRealized, childInput, childExtended, childOccurrence, childRows⟩ :=
    accepted_generated_while_header_condition source selected owned occurrence rows admitted realized input headerEq lowered extended
  have progress := family child childOwner childOccurrence childRows coverage childAdmitted bounded childRealized childInput childExtended steps stopped nonTimeout
  exact ⟨child, ty, canonical, progress⟩

#print axioms accepted_generated_while_header_condition
#print axioms accepted_generated_while_header_prefix
#print axioms accepted_generated_while_header_stopped
end Goose.Lower

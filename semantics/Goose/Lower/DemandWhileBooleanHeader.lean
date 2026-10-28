import Goose.Lower.DemandWhileHeaderCondition
import Goose.Lower.DemandBooleanCursor

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_while_boolean_header_prefix {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state : St} (source : StmtSource cfg env (.while condition body origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before headerState built : LS} {header : BlockId}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement none (.while condition body origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {frame : GIR.Frame} (realized : map.Realizes cfg.mod source.world env ⟨(header, 0), frame, state⟩)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv headerState frame (header, 0))
    (headerEq : headerState = demandWhileHeaderBefore (lowerEnv cfg.mod env.vars results) before)
    (coverage : map.Covers required) (bounded : map.Bounded headerState.vals.size)
    (fragment : BooleanNotExpression condition)
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) headerState = ((), built)) (extended : ExtT built cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨(header, 0), frame, state⟩ reached) :
    ∃ child : ExprSource cfg env condition state, child.ty = .bool ∧
      source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]) ∧
      DemandPrefixDecomposition cx (fun fuel => evalExpr fuel cfg env condition) (GeneratedUniformExpressionCursor cx child headerState
          (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2 frame (header, 0) map required)
        (GeneratedExpressionPrefixEnd child map cx headerState frame
          (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2
          (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1)
        taken ⟨(header, 0), frame, state⟩ reached := by
  obtain ⟨child, ty, canonical, childOwner, childAdmitted, childRealized, childInput, childExtended, childOccurrence, childRows⟩ :=
    accepted_generated_while_header_condition source selected owned occurrence rows admitted realized input headerEq lowered extended
  have family : GeneratedExpressionPrefixFamily cx results selected none condition (@GeneratedUniformExpressionCursor cfg env cx) :=
    accepted_generated_boolean_uniform_prefix_family selected none fragment
  have progress := family child childOwner childOccurrence childRows coverage childAdmitted bounded childRealized childInput childExtended steps
  exact ⟨child, ty, canonical, progress.progress⟩


theorem accepted_generated_while_boolean_header_maximal {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state : St} (source : StmtSource cfg env (.while condition body origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before headerState built : LS} {header : BlockId}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement none (.while condition body origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {frame : GIR.Frame} (realized : map.Realizes cfg.mod source.world env ⟨(header, 0), frame, state⟩)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv headerState frame (header, 0))
    (headerEq : headerState = demandWhileHeaderBefore (lowerEnv cfg.mod env.vars results) before)
    (coverage : map.Covers required) (bounded : map.Bounded headerState.vals.size)
    (fragment : BooleanNotExpression condition)
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) headerState = ((), built)) (extended : ExtT built cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨(header, 0), frame, state⟩ reached)
    {fuel : Nat} (maximal : ∀ next, ¬ DemandInstructionStep cx fuel reached next) :
    ∃ (child : ExprSource cfg env condition state), child.ty = .bool ∧
      source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]) ∧
      ∃ (sourceFuel consumed remaining : Nat) (boundary : DemandRuntimePoint) (value : Val),
        consumed + remaining = taken ∧ DemandRuntimePrefix cx consumed ⟨(header, 0), frame, state⟩ boundary ∧
        DemandRuntimePrefix cx remaining boundary reached ∧ evalExpr sourceFuel cfg env condition state = .ok value boundary.state ∧
        GeneratedExpressionPrefixEnd child map cx headerState frame
          (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2
          (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1 value boundary := by
  obtain ⟨child, ty, canonical, progress⟩ := accepted_generated_while_boolean_header_prefix source selected owned occurrence rows
    admitted realized input headerEq coverage bounded fragment lowered extended steps
  refine ⟨child, ty, canonical, ?_⟩
  cases progress with
  | interior cursor =>
    obtain ⟨next, step⟩ := cursor.next
    exact (maximal next (step fuel)).elim
  | complete count executed residual evaluated post =>
    exact ⟨_, _, _, _, _, count, executed, residual, evaluated, post⟩

#print axioms accepted_generated_while_boolean_header_prefix
#print axioms accepted_generated_while_boolean_header_maximal
end Goose.Lower

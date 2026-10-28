import Goose.Lower.DemandCallSliceRetained
import Goose.Lower.DemandControlProgressCursor
import Goose.Lower.DemandExpressionFuture

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem SliceSlotArgumentCell.atControlCursor {cfg : Cfg} {env : Env} {initialState state : St}
    {contextId : ContextId} {arguments : List Arg} {origin : OriginId}
    {root : ExprSource cfg env (.call contextId arguments origin) initialState}
    {offset : Nat} {initial : GIR.Frame} {cell : SliceSlotArgumentCell}
    (checked : cell.Checked root offset initial)
    {cx : FnCtx} {expression : Expr} {source : ExprSource cfg env expression state}
    {before built : LS} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : GeneratedControlProgressCursor cx source before built initial start map required runtime)
    (bounded : cell.value < before.vals.size) : cell.Checked root offset runtime.frame := by
  obtain ⟨found, prior, visible, descriptorAt, scope, descriptorType, annotation, aliasType, valueAt⟩ := checked
  refine ⟨found, prior, visible, descriptorAt, scope, descriptorType, annotation, aliasType, ?_⟩
  rw [cursor.same cell.value bounded]
  exact valueAt

theorem SliceSlotArgumentCells.ofLaterValueCursor {cfg : Cfg} {env : Env} {initialState state : St}
    {contextId : ContextId} {arguments : List Arg} {origin : OriginId}
    (root : ExprSource cfg env (.call contextId arguments origin) initialState)
    {offset : Nat} {expression : Expr} (current : arguments[offset]? = some (.byVal expression))
    (child : ExprSource cfg env expression state)
    (canonical : (ArgSource.byVal child).MatchesContext root.world root.typingEnv root.rootsEnv
      (callArgContext root.context offset (.byVal expression) current))
    {cx : FnCtx} {before built : LS} {initial : GIR.Frame} {start : Pt}
    {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : GeneratedControlProgressCursor cx child before built initial start map required runtime)
    (cells : List SliceSlotArgumentCell) (checked : ∀ cell ∈ cells, cell.Checked root offset initial)
    (bounded : ∀ cell ∈ cells, cell.value < before.vals.size) :
    SliceSlotArgumentCells.Realizes cells cfg.mod root.world env runtime := by
  intro cell member
  have currentCell := SliceSlotArgumentCell.atControlCursor (checked cell member) cursor (bounded cell member)
  obtain ⟨found, prior, visible, variableAt, scope, variableType, annotation, aliasType, valueAt⟩ := currentCell
  obtain ⟨plans, path, world, typing, roots, childContext⟩ := canonical
  have contextEq : HEq child.context
      (root.context.child rfl offset (.expression expression) .expression
        (by simp [DemandNode.child?, DemandNode.children, current]) (by trivial)) := by
    simpa only [ArgSource.MatchesContext, callArgContext] using childContext
  have futureEq := demandContextOutputFutureEq plans path rfl contextEq
  have needed := callArgContext_priorSliceHolder_output root.context root.active root.access root.frame.vars_t
    variableAt variableType visible current found prior
  have childNeeded : cell.slot ∈ child.context.outputFuture := by
    rw [futureEq]
    simpa only [callArgContext, ArgContext.outputFuture] using needed
  obtain ⟨future, demanded, source⟩ := cursor.demanded.futureFrame childNeeded
  have childVisible : cell.slot ∈ child.typingEnv.visible := by simpa only [typing] using visible
  have childAnnotation : child.rootsEnv.ann cell.slot = some cell.alias.roots := by simpa only [roots] using annotation
  have result := SliceSlotAliasAt.ofFrame source childVisible demanded variableAt scope variableType childAnnotation aliasType valueAt
  simpa only [world] using result

#print axioms SliceSlotArgumentCells.ofLaterValueCursor

#print axioms SliceSlotArgumentCell.atControlCursor
end Goose.Lower

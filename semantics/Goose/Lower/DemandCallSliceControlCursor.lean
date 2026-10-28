import Goose.Lower.DemandCallSliceRetained
import Goose.Lower.DemandControlProgressCursor

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

#print axioms SliceSlotArgumentCell.atControlCursor
end Goose.Lower

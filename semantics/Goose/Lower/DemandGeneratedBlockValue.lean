import Goose.Lower.DemandGeneratedBody
import Goose.Lower.DemandExpressionResult

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_block_value_entry {cfg : Cfg} {env : Env} {stmts : List Stmt}
    {state after : St} (source : StmtsSource cfg env stmts state)
    {expression : Expr} (hasValue : source.value = some expression) {ty : Ty} {typingEnd : Nat}
    {roots : List RootRef} {rootsEnd : RState}
    (typed : tyExpr source.typingAfter expression source.typingEnd = .ok (ty, typingEnd))
    (rooted : rpExpr source.rootsEnv expression source.rootsEnd = .ok (roots, rootsEnd))
    (effects : EffLe rootsEnd.eff source.world.E)
    {fuel : Nat} (evaluated : execStmts fuel cfg env stmts state = .ok (.normal .unit) after)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before start : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {want : Bool} {block : Core.Block}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop bindings want block) before)
    (all : source.all = block.stmts) (scope : source.scope = block.scope) (value : source.value = block.value)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded start.vals.size) {initial frame : GIR.Frame} {initialPoint point : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨initialPoint, initial, state⟩)
    (post : Post cfg env cx start initial
      (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block) frame point []) :
    ∃ child : ExprSource cfg env expression after,
      child.typingEnv = source.typingAfter ∧ child.rootsEnv = source.rootsEnv ∧ child.ty = ty ∧
      source.ValueChildAt expression hasValue child ∧
      DemandNode.block (.mk source.scope source.all source.value) = .block block ∧
    ∃ childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root child.path (.expression expression)
        (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block),
      GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required ∧ map.Covers required ∧
      map.Admitted cfg.mod.profile child.context.retained ∧
      map.Bounded (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block).vals.size ∧
      DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.inputFuture
        map.values map.runs ⟨point, frame, after⟩ := by
  obtain ⟨child, typingEq, rootsEq, typeEq, canonical⟩ :=
    source.valueChild expression hasValue ty typingEnd roots rootsEnd typed rooted effects fuel .unit evaluated
  have valueAt : block.value = some expression := value.symm.trans hasValue
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root child.path (.expression expression)
      (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block) := by
    rw [canonical.path, all]
    exact .blockValue occurrence valueAt
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.blockValue occurrence valueAt) required :=
      .blockValue (valueAt := valueAt) rows
    simpa only [rootsEq, canonical.path, all, demandBlockValueBefore] using inherited
  have childAdmitted : map.Admitted cfg.mod.profile child.context.retained :=
    fun profile alias member => canonical.retained alias (admitted profile alias member)
  have result := source.result fuel (.normal .unit) evaluated
  have retained : RetainsAliases cfg.mod source.world env state.store after.store
      (map.values.map Prod.snd ++ map.runs.map Prod.snd) := by
    cases profile : cfg.mod.profile with
    | pilot => exact retainedAliases_of_storeLe (result.pilotStore profile) _
    | shrink => exact result.aliases.subset (admitted profile)
  have carried := realized.retained post.same bounded.1 bounded.2 retained
  have childCarried : map.Realizes cfg.mod child.world env ⟨point, frame, after⟩ := by
    simpa only [RetainedSsaMap.Realizes, canonical.world] using carried
  refine ⟨child, typingEq, rootsEq, typeEq, canonical, ?_, childOccurrence, childRows, coverage,
    childAdmitted, bounded.mono post.mono, ⟨⟨_, post.pp, post.rel⟩, child.frame, childCarried⟩⟩
  rw [scope, all, value]
  cases block
  rfl

end Goose.Lower

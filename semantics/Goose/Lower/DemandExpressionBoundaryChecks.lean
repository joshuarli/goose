import Goose.Lower.DemandExpressionBoundary
import Goose.Lower.TypedExpressionChecks
import Goose.Lower.LifetimeChecks

namespace Goose.Lower.DemandExpressionBoundaryChecks

open Goose.Core Goose.GIR Goose.Core.Sound

private def emptyMap : RetainedSsaMap := ⟨[], []⟩

theorem accepted_call_boundary (profile : NumProfile)
    {before built : LS} {id : ValueId} {point : Pt} {cx : FnCtx} {frame : GIR.Frame}
    (lowered : lowerExpr (.call 1 [.byVal (.bool true), .byVal (.bool false)] 0)
      (lowerEnv TypedExpressionChecks.sourceModule #[] []) before = (id, built))
    (atPoint : before.pp = some point) (extension : ExtT built cx.fn.blocks)
    (related : Rel ⟨profile, TypedExpressionChecks.sourceModule⟩ TypedExpressionChecks.sourceEnv cx frame before)
    (moduleEq : cx.cfg.mod = lower TypedExpressionChecks.sourceModule)
    (resultsEq : cx.fn.results = []) (generated : GeneratedBuilderState before) (fuel : Nat) :
    ReflectAtFuel fuel cx point frame
      (fun sourceFuel => evalExpr sourceFuel ⟨profile, TypedExpressionChecks.sourceModule⟩
        TypedExpressionChecks.sourceEnv (.call 1 [.byVal (.bool true), .byVal (.bool false)] 0))
      (ExpressionDemandBoundary (TypedExpressionChecks.callSource profile) emptyMap cx before frame built id)
      TypedExpressionChecks.enteredState := by
  have metadata : SourceResults (TypedExpressionChecks.callSource profile).typingEnv
      (TypedExpressionChecks.callSource profile).rootsEnv [] := by
    intro impl present
    change some TypedExpressionChecks.sourceImpl = some impl at present
    cases present
    exact ⟨rfl, rfl⟩
  refine accepted_expression_demand_reflection (TypedExpressionChecks.callSource profile) metadata emptyMap
    ?_ ?_ ?_ lowered atPoint extension related moduleEq resultsEq generated fuel
  · intro shrink
    cases shrink
  · constructor <;> simp [emptyMap]
  · constructor <;> simp [emptyMap]

theorem pushed_reference_uses_checked_roots {profile : NumProfile} {artifact : ArtifactProfile} {capacity : Nat}
    {env : Env} {state after : St}
    {source : ExprSource ⟨profile, TypedExpressionChecks.pushModule artifact capacity⟩ env
      (.push (.global 0) (.bool true) (TypedExpressionChecks.pushOrigin artifact)) state}
    {map : RetainedSsaMap} {cx : FnCtx} {before built : LS} {initial frame : GIR.Frame}
    {id : ValueId} {value : Val} {point : Pt}
    (boundary : ExpressionDemandBoundary source map cx before initial built id value after point frame) :
    ValueAliasAt (TypedExpressionChecks.pushModule artifact capacity) source.world env after.store frame id
      ⟨.ref .mutable .bool, [.global 0], .operand source.path⟩ := by
  have query : source.rootsEnv.access.aliasExpr source.path
      (.push (.global 0) (.bool true) (TypedExpressionChecks.pushOrigin artifact)) =
      .ok [⟨.ref .mutable .bool, [.global 0], .operand source.path⟩] := by
    cases artifact <;>
      simp [AccessEnv.aliasExpr, AccessEnv.exprType?, AccessEnv.placeType?, AccessEnv.exprRoots,
        AccessEnv.placeRoots, PEnv.access, source.frame.mod_p, TypedExpressionChecks.pushModule,
        TypedExpressionChecks.pushOwnerType, Ty.ownerElem?, Ty.interiorTarget?]
    all_goals rfl
  exact boundary.canonical _ query _ (by simp)

theorem removed_run_cannot_be_boundary {cfg : Cfg} {env : Env} {expression : Expr} {state : St}
    {source : ExprSource cfg env expression state} {map : RetainedSsaMap} {cx : FnCtx}
    {before built : LS} {initial : GIR.Frame} {id : ValueId} {value : Val} {point : Pt}
    {alias : RetainedAlias} (member : (0, alias) ∈ map.runs) :
    ¬ ExpressionDemandBoundary source map cx before initial built id value LifetimeChecks.removedSample
      point LifetimeChecks.sampledFrame := by
  intro boundary
  exact LifetimeChecks.removed_sample_not_retained cfg.mod source.world env alias
    (boundary.demanded.operands.2 (0, alias) member)

end Goose.Lower.DemandExpressionBoundaryChecks

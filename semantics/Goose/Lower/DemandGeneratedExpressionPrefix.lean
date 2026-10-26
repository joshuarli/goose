import Goose.Lower.DemandGeneratedStatementPrefix
import Goose.Lower.DemandGeneratedScalarSteps

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

abbrev GeneratedExpressionPrefixEnd {cfg : Cfg} {env : Env} {expression : Expr} {state : St}
    (source : ExprSource cfg env expression state) (map : RetainedSsaMap) (cx : FnCtx)
    (before : LS) (initial : GIR.Frame) (built : LS) (id : ValueId) : Val → DemandRuntimePoint → Prop :=
  fun value runtime => ExpressionDemandBoundary source map cx before initial built id value runtime.state runtime.point runtime.frame

structure GeneratedExpressionPrefixDecomposition {cfg : Cfg} {env : Env} {expression : Expr} {state : St}
    (source : ExprSource cfg env expression state) {cx : FnCtx} {results : List Ty} {root : DemandNode}
    {owner : Nat} {before : LS}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression expression) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (map : RetainedSsaMap) (initial : GIR.Frame) (start : Pt) (cursor : DemandRuntimePoint → Prop)
    (taken : Nat) (reached : DemandRuntimePoint) : Prop where
  sourceOwner : GeneratedSourceOwner selected source.context
  coverage : map.Covers required
  progress : DemandPrefixDecomposition cx (fun fuel => evalExpr fuel cfg env expression)
    cursor (GeneratedExpressionPrefixEnd source map cx before initial
      (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).2
      (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).1)
    taken ⟨start, initial, state⟩ reached

def GeneratedExpressionPrefixFamily {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (expression : Expr)
    (cursor : ∀ {expression : Expr} {state : St}, ExprSource cfg env expression state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop) : Prop :=
  ∀ {state : St} (source : ExprSource cfg env expression state) {before : LS}
    (_owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression expression) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required),
    map.Covers required → map.Admitted cfg.mod.profile source.context.retained → map.Bounded before.vals.size →
    ∀ {initial : GIR.Frame} {start : Pt}, map.Realizes cfg.mod source.world env ⟨start, initial, state⟩ →
    GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start →
    ExtT (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks →
    ∀ {taken : Nat} {reached : DemandRuntimePoint}, DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached →
    GeneratedExpressionPrefixDecomposition source selected occurrence rows map initial start
      (cursor source before (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).2 initial start map required)
      taken reached

structure GeneratedExpressionPrefixLeafCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    {expression : Expr} {state : St} (source : ExprSource cfg env expression state)
    (before built : LS) (initial : GIR.Frame) (start : Pt) (map required : RetainedSsaMap)
    (runtime : DemandRuntimePoint) : Prop where
  site : ∃ form : ScalarExpression expression, form.boundary = .entry ∧
    GeneratedScalarSite form cfg.mod source.rootsEnv.access cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path before required runtime.point
  sourceOwner : GeneratedSourceOwner selected source.context
  lowered : built = (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).2
  atEntry : runtime = ⟨start, initial, state⟩
  coverage : map.Covers required
  admitted : map.Admitted cfg.mod.profile source.context.retained
  bounded : map.Bounded before.vals.size
  atPoint : before.pp = some runtime.point
  related : Rel cfg env cx runtime.frame before
  demanded : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.inputFuture
    map.values map.runs runtime

private theorem scalar_entry_label {expression : Expr} (form : ScalarExpression expression)
    (entry : form.boundary = .entry) (path : List Nat) : form.label path = ⟨path, .expression, .entry⟩ := by
  cases form <;> simp_all [ScalarExpression.boundary, ScalarExpression.label, ScalarExpression.ownerPath]

theorem GeneratedExpressionPrefixLeafCursor.instruction {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {expression : Expr} {state : St} {source : ExprSource cfg env expression state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : GeneratedExpressionPrefixLeafCursor cx results selected source before built initial start map required runtime) :
    ∃ instruction, GeneratedScalarInstruction cfg.mod source.rootsEnv.access cx.fn required
      ⟨source.path, .expression, .entry⟩ runtime.point instruction ∧ instAt cx.fn runtime.point = some instruction := by
  obtain ⟨form, entry, generated⟩ := cursor.site
  have site := GeneratedScalarInstruction.scalar form generated
  refine ⟨_, ?_, generated.instruction⟩
  simpa only [scalar_entry_label form entry] using site

theorem GeneratedExpressionPrefixLeafCursor.rows {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {expression : Expr} {state : St} {source : ExprSource cfg env expression state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : GeneratedExpressionPrefixLeafCursor cx results selected source before built initial start map required runtime) :
    ∃ occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root source.path (.expression expression) before,
      GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required := by
  obtain ⟨form, entry, site⟩ := cursor.site
  refine ⟨site.occurrence, ?_⟩
  cases form <;> try cases entry
  all_goals exact site.rows

theorem GeneratedExpressionPrefixLeafCursor.frame {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {expression : Expr} {state : St} {source : ExprSource cfg env expression state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : GeneratedExpressionPrefixLeafCursor cx results selected source before built initial start map required runtime) :
    DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.inputFuture
      map.values map.runs runtime := cursor.demanded

theorem GeneratedExpressionPrefixLeafCursor.realizes {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {expression : Expr} {state : St} {source : ExprSource cfg env expression state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : GeneratedExpressionPrefixLeafCursor cx results selected source before built initial start map required runtime) :
    map.Realizes cfg.mod source.world env runtime := cursor.demanded.operands

theorem accepted_generated_expression_leaf_prefix {cfg : Cfg} {env : Env} {expression : Expr}
    (form : ScalarExpression expression) (entry : form.boundary = .entry) (inputs : form.Inputs) {state : St}
    (source : ExprSource cfg env expression state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression expression) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (atPoint : before.pp = some start) (related : Rel cfg env cx initial before)
    (extended : ExtT (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    GeneratedExpressionPrefixDecomposition source selected occurrence rows map initial start
      (GeneratedExpressionPrefixLeafCursor cx results selected source before
        (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).2 initial start map required) taken reached := by
  let le := lowerEnv cfg.mod env.vars results
  have prefixEq : form.prefix le before = before := by
    cases form <;> simp_all [ScalarExpression.boundary, ScalarExpression.prefix]
  have cellsEq : form.cells le before inputs = [] := by
    cases form <;> simp_all [ScalarExpression.boundary, ScalarExpression.cells]
  have prefixEvaluated : form.PrefixEvaluated inputs 0 cfg env state state := by
    cases form <;> simp_all [ScalarExpression.boundary, ScalarExpression.PrefixEvaluated]
  have leafRows : GeneratedDemandRows cfg.mod source.rootsEnv.access (form.ownerOccurrence occurrence) required := by
    cases form <;> try cases entry
    all_goals exact rows
  have site : GeneratedScalarSite form cfg.mod source.rootsEnv.access cx.fn le root source.path before required start :=
    ⟨occurrence, leafRows, by simpa only [prefixEq] using atPoint, extended⟩
  have post : Post cfg env cx before initial (form.prefix le before) initial start (form.cells le before inputs) := by
    rw [prefixEq, cellsEq]
    exact Post.init related atPoint
  refine ⟨owned, coverage, ?_⟩
  rcases steps.uncons with ⟨rfl, rfl⟩ | ⟨remaining, current, rfl, actual, residual⟩
  · exact .interior ⟨⟨form, entry, site⟩, owned, rfl, rfl, coverage, admitted, bounded, atPoint, related,
      ⟨⟨_, atPoint, related⟩, source.frame, realized⟩⟩
  · obtain ⟨_, _, _, _, _, _, value, _, _, _, _, evaluated, boundary⟩ :=
      accepted_generated_scalar_runtime_step form inputs source prefixEvaluated site coverage post
        (by simpa only [prefixEq] using bounded) realized actual
    exact .complete (by omega) (.next actual (.zero _)) residual evaluated boundary

theorem accepted_generated_literal_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (type : IntTy) (number : Int) :
    GeneratedExpressionPrefixFamily cx results selected loop (.lit type number)
      (@GeneratedExpressionPrefixLeafCursor cfg env cx results root owner selected) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  exact accepted_generated_expression_leaf_prefix (.literal type number) rfl () source selected owned occurrence rows
    coverage admitted bounded realized input.atPoint input.related extended steps

theorem accepted_generated_boolean_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (value : Bool) :
    GeneratedExpressionPrefixFamily cx results selected loop (.bool value)
      (@GeneratedExpressionPrefixLeafCursor cfg env cx results root owner selected) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  exact accepted_generated_expression_leaf_prefix (.boolean value) rfl () source selected owned occurrence rows
    coverage admitted bounded realized input.atPoint input.related extended steps

end Goose.Lower

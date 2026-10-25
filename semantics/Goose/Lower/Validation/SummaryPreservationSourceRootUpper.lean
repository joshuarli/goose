import Goose.Lower.Validation.SourceRootBounds
import Goose.Lower.Validation.SummaryPreservationRefinedResults

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem source_expr_context_upper (expression : Expr) {env : TEnv} {penv : PEnv}
    (tables : SourceRootTables env penv) (accepted : Core.validate penv.mod = .ok ())
    {context : ContextId} (contextAt : penv.mod.contexts[context]? = some penv.ctx)
    (implAt : penv.mod.impls[penv.ctx.impl]? = some penv.impl)
    {ty : Ty} {start finish : Nat} (typed : tyExpr env expression start = .ok (ty, finish))
    {before after : RState} {sourceRoots actual : List RootRef}
    (replayed : rpExpr penv expression before = .ok (sourceRoots, after))
    (refined : RootsRefine (lowerContextAt penv.mod penv.ctx penv.impl) actual sourceRoots) :
    ∀ root ∈ actual,
      root ∈ refinedResultUpper (lowerContextAt penv.mod penv.ctx penv.impl) sourceRoots :=
  rootsRefine_context_upper refined
    (source_expr_param_bounds expression tables accepted contextAt implAt typed replayed)

theorem source_place_context_upper (place : Place) {env : TEnv} {penv : PEnv}
    (tables : SourceRootTables env penv) (accepted : Core.validate penv.mod = .ok ())
    {context : ContextId} (contextAt : penv.mod.contexts[context]? = some penv.ctx)
    (implAt : penv.mod.impls[penv.ctx.impl]? = some penv.impl)
    {info : PlaceInfo} {start finish : Nat} (typed : tyPlace env place start = .ok (info, finish))
    {before after : RState} {sourceRoots actual : List RootRef}
    (replayed : rpPlace penv place before = .ok (sourceRoots, after))
    (refined : RootsRefine (lowerContextAt penv.mod penv.ctx penv.impl) actual sourceRoots) :
    ∀ root ∈ actual,
      root ∈ refinedResultUpper (lowerContextAt penv.mod penv.ctx penv.impl) sourceRoots :=
  rootsRefine_context_upper refined
    (source_place_param_bounds place tables accepted contextAt implAt typed replayed)

theorem source_view_context_upper (view : View) {env : TEnv} {penv : PEnv}
    (tables : SourceRootTables env penv) (accepted : Core.validate penv.mod = .ok ())
    {context : ContextId} (contextAt : penv.mod.contexts[context]? = some penv.ctx)
    (implAt : penv.mod.impls[penv.ctx.impl]? = some penv.impl)
    {info : Ty × Bool} {start finish : Nat} (typed : tyView env view start = .ok (info, finish))
    {before after : RState} {sourceRoots actual : List RootRef}
    (replayed : rpView penv view before = .ok (sourceRoots, after))
    (refined : RootsRefine (lowerContextAt penv.mod penv.ctx penv.impl) actual sourceRoots) :
    ∀ root ∈ actual,
      root ∈ refinedResultUpper (lowerContextAt penv.mod penv.ctx penv.impl) sourceRoots :=
  rootsRefine_context_upper refined
    (source_view_param_bounds view tables accepted contextAt implAt typed replayed)

end Goose.Lower.Validation.SummaryPreservation

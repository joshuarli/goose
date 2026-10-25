import Goose.Lower.Validation.SummaryPreservationSourceReturnScalar
import Goose.Lower.Validation.SummaryPreservationReturnLedger

namespace Goose.Lower.Validation.SummaryPreservation.BuilderReturnsBound

open Goose.Core Goose.GIR

theorem returned_scalar_expression {env output : TEnv} {impl : Impl} {expression : Expr}
    {sourceOrigin : OriginId} {scope start finish : Nat} {actual : Ty}
    {func : Func} {le : LEnv} {scopeCount : Nat} {initial expressionState returnedState : LS}
    {oldUpper childUpper newUpper : Prov} {target : List RootRef} {sourceRoots : List RootRef}
    {value returned : ValueId} (loop : Option LoopCtx)
    (prior : BuilderReturnsBound oldUpper target initial)
    (symbols : initial.SymbolWF le scopeCount) (size : oldUpper.vals.size = initial.vals.size)
    (generated : GeneratedBuilderState initial)
    (source : Core.tyStmt env scope (.ret (some expression) sourceOrigin) start = .ok (output, finish))
    (implementation : env.impl = some impl)
    (nonref : (impl.results[0]?).any Ty.isRefLike = false)
    (resultTypes : le.results = impl.results.toList)
    (typed : Core.tyExpr env expression start = .ok (actual, finish))
    (expressionRun : lowerExpr expression le initial = (value, expressionState))
    (coercedRun : coerceResult value sourceOrigin le expressionState = (returned, returnedState))
    (child : expressionState.cur.isSome = true →
      ReplayValue func childUpper expressionState value sourceRoots (.data actual))
    (childSize : childUpper.vals.size = expressionState.vals.size)
    (retained : ∀ index, index < oldUpper.vals.size → rootsAt newUpper.vals index = rootsAt oldUpper.vals index)
    (childRetained : ∀ index, index < childUpper.vals.size → rootsAt newUpper.vals index = rootsAt childUpper.vals index) :
    BuilderReturnsBound newUpper target (lowerStmt loop (.ret (some expression) sourceOrigin) le initial).2 := by
  apply prior.returned_expression loop symbols size generated typed expressionRun coercedRun retained
  intro live root member
  have emptyRoots := source_return_scalar_roots source implementation nonref resultTypes typed child childSize
    coercedRun childRetained live
  rw [emptyRoots] at member
  cases member

end Goose.Lower.Validation.SummaryPreservation.BuilderReturnsBound

import Goose.Lower.Validation.SummaryPreservationReturnTransfer
import Goose.Lower.Validation.SummaryPreservationReturnFrames

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

theorem global_expression_returns {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {before : LS} {upper next : Prov}
    {env : TEnv} {expression : Expr} {type : Ty} {start finish : Nat}
    (expected : List RootRef)
    (source : Core.tyExpr env expression start = .ok (type, finish))
    (ready : ReplayBuilder module results vt func target le scopeCount slots before upper)
    (retained : ∀ old, old < upper.vals.size →
      rootsAt next.vals old = rootsAt upper.vals old) :
    ReturnBoundsPreserved expected before upper (lowerExpr expression le before).2 next :=
  .frame ready.symbols ready.roots.valueSize retained
    (source_expression_return_frame source le before _ _ rfl)

theorem global_place_returns {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {before : LS} {upper next : Prov}
    {env : TEnv} {place : Place} {type : PlaceInfo} {start finish : Nat}
    (expected : List RootRef)
    (source : Core.tyPlace env place start = .ok (type, finish))
    (ready : ReplayBuilder module results vt func target le scopeCount slots before upper)
    (retained : ∀ old, old < upper.vals.size →
      rootsAt next.vals old = rootsAt upper.vals old) :
    ReturnBoundsPreserved expected before upper (lowerPlace place le before).2 next :=
  .frame ready.symbols ready.roots.valueSize retained
    (source_place_return_frame source le before _ _ rfl)

theorem global_view_returns {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {before : LS} {upper next : Prov}
    {env : TEnv} {view : View} {type : Ty × Bool} {start finish : Nat}
    (expected : List RootRef)
    (source : Core.tyView env view start = .ok (type, finish))
    (ready : ReplayBuilder module results vt func target le scopeCount slots before upper)
    (retained : ∀ old, old < upper.vals.size →
      rootsAt next.vals old = rootsAt upper.vals old) :
    ReturnBoundsPreserved expected before upper (lowerView view le before).2 next :=
  .frame ready.symbols ready.roots.valueSize retained
    (source_view_return_frame source le before _ _ rfl)

#print axioms global_expression_returns
#print axioms global_place_returns
#print axioms global_view_returns

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

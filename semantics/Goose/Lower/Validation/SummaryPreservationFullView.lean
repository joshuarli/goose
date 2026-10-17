import Goose.GIR.Effects
import Goose.GIR.Eval

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem execPure_full_viewSlice {context : FnCtx} {frame : Frame} {value : ValueId}
    {view : ViewVal} (lookup : frame.vals[value]? = some (.view view))
    (mutability : Mutability) (origin : Option OriginId) (state : St) :
    execPure context frame (.viewSlice mutability value .omitted .omitted origin) state =
      .ok (.val (.slice view.loc view.start view.len)) state := by
  simp [execPure, getView, getCell, lookup, evalBnd, bind, pure, M.bind', M.pure']

theorem effectStep_full_viewSlice (module : GIR.Module) (vt : Array (Option VTy))
    (func : Func) (provenance : Prov) (effect : Core.Eff) (result value : ValueId)
    (mutability : Mutability) (origin : Option OriginId) :
    func.effectStep module vt provenance effect
      (.def result (.viewSlice mutability value .omitted .omitted origin)) = effect := rfl


theorem effectStep_bounded_viewSlice (module : GIR.Module) (vt : Array (Option VTy))
    (func : Func) (provenance : Prov) (effect : Core.Eff) (result value : ValueId)
    (mutability : Mutability) (low high : Bnd) (origin : Option OriginId)
    (bounded : low ≠ .omitted ∨ high ≠ .omitted) :
    func.effectStep module vt provenance effect
      (.def result (.viewSlice mutability value low high origin)) = { effect with aborts := true } := by
  cases low <;> cases high <;> simp_all [Func.effectStep]

theorem execPure_negative_lower_viewSlice {context : FnCtx} {frame : Frame}
    {value lower : ValueId} {view : ViewVal}
    (viewLookup : frame.vals[value]? = some (.view view))
    (lowerLookup : frame.vals[lower]? = some (.val (.int .i64 (-1))))
    (mutability : Mutability) (origin : OriginId) (state : St) :
    execPure context frame (.viewSlice mutability value (.val lower) .omitted (some origin)) state =
      .stop (.abort .sliceOob origin) state := by
  simp [execPure, getView, getVal, getCell, viewLookup, lowerLookup, evalBnd, expectInt,
    bind, pure, M.bind', M.pure', abortAtOrg, abortAt, M.stop]

end Goose.Lower.Validation.SummaryPreservation

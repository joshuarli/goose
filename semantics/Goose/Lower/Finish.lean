import Goose.Lower.Prefix
import Goose.Lower.Validate

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem advB_finishFunction (impl : Impl) (v : ValueId) : AdvB (finishFunction impl v) := by
  unfold finishFunction
  refine AdvB.bind advB_read fun le => AdvB.bind advB_isLive fun live => ?_
  cases live with
  | false => exact AdvB.pure _
  | true =>
    by_cases h : (!impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges le.mod.noReturn) = true
    · rw [if_pos h]
      exact advB_header0 fun sink => advB_emitTerm (.br sink [])
    · rw [if_neg h]
      exact advB_emitTerm _

theorem finishFunction_nondivergent (impl : Impl) (le : LEnv) (ls : LS) (v : ValueId)
    (hd : impl.body.diverges le.mod.noReturn = false) :
    finishFunction impl v le ls =
      ((do if (← isLive) then
        emitTerm (.ret (if impl.body.value.isSome then [v] else []) none) : B Unit) le ls) := by
  simp [finishFunction, bind_run, read_apply, hd]

end Goose.Lower

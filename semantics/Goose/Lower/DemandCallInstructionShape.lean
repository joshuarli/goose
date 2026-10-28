import Goose.Lower.DemandCallActualSuccess

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem callOp_success_value {cx : FnCtx} {frame : GIR.Frame} {context : ContextId} {ids : List ValueId}
    {origin : Option OriginId} {fuel : Nat} {state after : St} {result : RVal}
    (executed : execOp fuel cx frame (.call context ids origin) state = .ok result after) :
    ∃ value : Val, result = .val value := by
  cases fuel with
  | zero => simp [execOp, timeout, M.stop] at executed
  | succ fuel =>
    simp only [execOp, bind_apply] at executed
    cases read : mapList (getVal frame) ids state with
    | stop reason final => simp [read] at executed
    | ok values middle =>
      simp only [read, bind_apply] at executed
      cases called : callFn fuel cx.cfg frame.depth context values middle with
      | stop reason final => simp [called] at executed
      | ok value final =>
        simp only [called, pure_apply, Res.ok.injEq] at executed
        exact ⟨value, executed.1.symm⟩

#print axioms callOp_success_value
end Goose.Lower

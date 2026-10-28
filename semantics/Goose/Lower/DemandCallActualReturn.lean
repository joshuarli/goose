import Goose.Lower.DemandCallActualEntry
import Goose.Lower.ReturnState

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem actual_call_return_step {cfg : GCfg} {caller callee : Func} {context : ContextId} {origin : OriginId}
    {ids : List ValueId} {values : List Val} {callerPoint : Pt} {callerFrame : GIR.Frame} {state : St} {result : ValueId}
    (instruction : instAt caller callerPoint = some (.def result (.call context ids (some origin))))
    (below : callerFrame.depth < maxCallDepth)
    (read : mapList (getVal callerFrame) ids state = .ok values state)
    (lookup : cfg.mod.funcs[context]? = some callee)
    {calleeFrame : GIR.Frame} {entered : St}
    (entry : FunctionEntry callee (callerFrame.depth + 1) values state calleeFrame entered)
    {taken extra : Nat} {terminal : DemandRuntimePoint} {value : Val} {returnOrigin : OriginId}
    (steps : DemandPrefix ⟨cfg, callee⟩ taken (taken + extra + 1) ⟨(0, 0), calleeFrame, entered⟩ terminal)
    (returned : ReturnSite ⟨cfg, callee⟩ terminal.point terminal.frame value returnOrigin) :
    RuntimeStep cfg caller callerPoint callerFrame state (callerPoint.1, callerPoint.2 + 1)
      (callerFrame.set result (.val value)) terminal.state := by
  have calleeRun : runAt ⟨cfg, callee⟩ (0, 0) calleeFrame (taken + extra + 1) entered = .ok value terminal.state := by
    rw [steps.runAt]
    have fuelEq : taken + extra + 1 - taken = extra + 1 := by omega
    simpa only [fuelEq] using returned.run terminal.state extra
  have enteredRun : enterFn (taken + extra + 2) cfg (callerFrame.depth + 1) callee values state = .ok value terminal.state := by
    simpa only [FunctionEntry.enterFn] using (entry.enterFn (taken + extra + 1)).trans calleeRun
  have callRun : execOp (taken + extra + 4) ⟨cfg, caller⟩ callerFrame (.call context ids (some origin)) state =
      .ok (.val value) terminal.state := by
    simp only [execOp, bind_apply, read, callFn, Nat.not_le_of_lt below, ↓reduceIte, lookupFn, lookup, pure_apply, enteredRun]
  exact .define instruction callRun

#print axioms actual_call_return_step
end Goose.Lower

import Goose.Lower.DemandCallActualEntry
import Goose.Lower.ReturnState

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem DemandPrefix.monoFuel {cx : FnCtx} {taken fuel larger : Nat} {before after : DemandRuntimePoint}
    (steps : DemandPrefix cx taken fuel before after) (bound : fuel ≤ larger) :
    DemandPrefix cx taken larger before after := by
  induction steps generalizing larger with
  | zero => exact .zero _ _
  | @next length fuel before middle after step rest ih =>
    cases larger with
    | zero => omega
    | succ larger =>
      have lower : fuel ≤ larger := by omega
      exact .next (step.mono_fuel lower) (ih lower)

theorem DemandRuntimePrefix.fueled {cx : FnCtx} {taken : Nat} {before after : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken before after) :
    ∃ extra, DemandPrefix cx taken (taken + extra + 1) before after := by
  induction steps with
  | zero => exact ⟨0, .zero _ _⟩
  | @next length before middle after step rest ih =>
    obtain ⟨extra, tail⟩ := ih
    obtain ⟨fuel, first⟩ := runtimeStep_demandInstructionStep step
    let enough := max fuel (length + extra + 1)
    have firstRaised := first.mono_fuel (Nat.le_max_left fuel (length + extra + 1))
    have tailRaised := tail.monoFuel (Nat.le_max_right fuel (length + extra + 1))
    have bound : length + 1 ≤ enough + 1 := by dsimp [enough]; omega
    refine ⟨enough - (length + 1), ?_⟩
    have equality : length + 1 + (enough - (length + 1)) + 1 = enough + 1 := by
      have enoughBound : length + 1 ≤ enough := by dsimp [enough]; omega
      omega
    rw [equality]
    exact .next firstRaised tailRaised

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

theorem actual_call_return_runtime_step {cfg : GCfg} {caller callee : Func} {context : ContextId} {origin : OriginId}
    {ids : List ValueId} {values : List Val} {callerPoint : Pt} {callerFrame : GIR.Frame} {state : St} {result : ValueId}
    (instruction : instAt caller callerPoint = some (.def result (.call context ids (some origin))))
    (below : callerFrame.depth < maxCallDepth)
    (read : mapList (getVal callerFrame) ids state = .ok values state)
    (lookup : cfg.mod.funcs[context]? = some callee)
    {calleeFrame : GIR.Frame} {entered : St}
    (entry : FunctionEntry callee (callerFrame.depth + 1) values state calleeFrame entered)
    {taken : Nat} {terminal : DemandRuntimePoint} {value : Val} {returnOrigin : OriginId}
    (steps : DemandRuntimePrefix ⟨cfg, callee⟩ taken ⟨(0, 0), calleeFrame, entered⟩ terminal)
    (returned : ReturnSite ⟨cfg, callee⟩ terminal.point terminal.frame value returnOrigin) :
    RuntimeStep cfg caller callerPoint callerFrame state (callerPoint.1, callerPoint.2 + 1)
      (callerFrame.set result (.val value)) terminal.state := by
  obtain ⟨extra, fueled⟩ := steps.fueled
  exact actual_call_return_step instruction below read lookup entry fueled returned

theorem actual_call_unit_return_runtime_step {cfg : GCfg} {caller callee : Func} {context : ContextId} {origin : OriginId}
    {ids : List ValueId} {values : List Val} {callerPoint : Pt} {callerFrame : GIR.Frame} {state : St} {result : ValueId}
    (instruction : instAt caller callerPoint = some (.def result (.call context ids (some origin))))
    (below : callerFrame.depth < maxCallDepth)
    (read : mapList (getVal callerFrame) ids state = .ok values state)
    (lookup : cfg.mod.funcs[context]? = some callee)
    {calleeFrame : GIR.Frame} {entered : St}
    (entry : FunctionEntry callee (callerFrame.depth + 1) values state calleeFrame entered)
    {taken : Nat} {terminal : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨cfg, callee⟩ taken ⟨(0, 0), calleeFrame, entered⟩ terminal)
    (returned : instAt callee terminal.point = some (.term (.ret [] none))) :
    RuntimeStep cfg caller callerPoint callerFrame state (callerPoint.1, callerPoint.2 + 1)
      (callerFrame.set result (.val .unit)) terminal.state := by
  obtain ⟨extra, fueled⟩ := steps.fueled
  have calleeRun : runAt ⟨cfg, callee⟩ (0, 0) calleeFrame (taken + extra + 1) entered = .ok .unit terminal.state := by
    rw [fueled.runAt]
    have fuelEq : taken + extra + 1 - taken = extra + 1 := by omega
    rw [fuelEq, runAt_ret0 returned extra]
    rfl
  have enteredRun : enterFn (taken + extra + 2) cfg (callerFrame.depth + 1) callee values state = .ok .unit terminal.state := by
    simpa only [FunctionEntry.enterFn] using (entry.enterFn (taken + extra + 1)).trans calleeRun
  have callRun : execOp (taken + extra + 4) ⟨cfg, caller⟩ callerFrame (.call context ids (some origin)) state =
      .ok (.val .unit) terminal.state := by
    simp only [execOp, bind_apply, read, callFn, Nat.not_le_of_lt below, ↓reduceIte, lookupFn, lookup, pure_apply, enteredRun]
  exact .define instruction callRun

#print axioms actual_call_unit_return_runtime_step
#print axioms DemandRuntimePrefix.fueled
#print axioms actual_call_return_step
#print axioms actual_call_return_runtime_step
end Goose.Lower

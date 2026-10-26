import Goose.Lower.DemandParameterPrefix
import Goose.Lower.DemandStateReflectionChecks
import Goose.Evidence.Execution

namespace Goose.Lower.DemandParameterPrefixChecks

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence
open DemandStateReflectionChecks

private def cfg : GCfg := ⟨.release, target⟩
private def callerState : St := { St.initial with nextAct := 1, nextScope := 1 }
private def callerFrame : GIR.Frame :=
  (((⟨0, [(0, 0)], {}, 1⟩ : GIR.Frame).set 0 (.val (.bool true))).set 1 (.val (.bool false))).set
    2 (.val (.bool true)) |>.set 3 (.val (.bool false))
private def calleeFrame : GIR.Frame :=
  ((⟨1, [], {}, 2⟩ : GIR.Frame).set 0 (.val (.bool true))).set 1 (.val (.bool false))
private def calleeState : St := { callerState with nextAct := 2 }
private def enteredFrame : GIR.Frame := { calleeFrame with scopes := [(0, 1)] }
private def enteredState : St := { calleeState with nextScope := 2 }
private def prefixState : St :=
  { enteredState with store := enteredState.store.introduce (.local 1 1 0) (.bool true) }

theorem actual_caller_point : RuntimePoint cfg caller (0, 5) callerFrame callerState := by
  have initial : RuntimePoint cfg caller (0, 0) ⟨0, [], {}, 1⟩
      { St.initial with nextAct := 1 } := by
    apply RuntimePoint.entry (fuel := 2) (before := St.initial)
    · decide
    · rfl
    · rfl
    · refine ⟨rfl, 0, { St.initial with nextAct := 1 }, rfl, ?_⟩
      rfl
  have entered := RuntimePoint.step initial (RuntimeStep.effect (effect := .enter 0) rfl rfl)
  have first := RuntimePoint.step entered (RuntimeStep.define (fuel := 0)
    (result := 0) (op := .constBool true) rfl rfl)
  have second := RuntimePoint.step first (RuntimeStep.define (fuel := 0)
    (result := 1) (value := .val (.bool false)) (st' := callerState) (op := .boolNot 0) rfl (by
      simp [execOp, execPure, getVal, getCell, Frame.set, callerState, St.initial,
        expectBool, bind_apply, pure_apply]))
  have third := RuntimePoint.step second (RuntimeStep.define (fuel := 0)
    (result := 2) (op := .constBool true) rfl rfl)
  exact RuntimePoint.step third (RuntimeStep.define (fuel := 0)
    (result := 3) (op := .constBool false) rfl rfl)

theorem actual_callee_entry : RuntimePoint cfg callee (0, 0) calleeFrame calleeState := by
  apply RuntimePoint.call actual_caller_point (callee := 1) (args := [2, 3])
    (origin := some 0) (values := [.bool true, .bool false]) (readState := callerState)
  · rfl
  · decide
  · simp [callerFrame, mapList, getVal, getCell, Frame.set, Std.HashMap.getElem_insert,
      bind_apply, pure_apply]
  · rfl
  · refine ⟨rfl, 1, calleeState, rfl, ?_⟩
    rfl

theorem actual_partial_parameter_point :
    RuntimePoint cfg callee (0, 2) enteredFrame prefixState := by
  have entered : RuntimePoint cfg callee (0, 1) enteredFrame enteredState :=
    RuntimePoint.step actual_callee_entry (RuntimeStep.effect (effect := .enter 0) rfl rfl)
  apply RuntimePoint.step entered
  apply RuntimeStep.effect (effect := .slotInit 0 0 (some 0)) rfl
  simp [execEff, slotRoot, callee, enteredFrame, calleeFrame, enteredState, calleeState,
    prefixState, callerState, getVal, getCell, Frame.set, Std.HashMap.getElem_insert,
    bind_apply, pure_apply]
  rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem actual_timeout_prefix : GIR.runModule 13 cfg St.initial = .stop .timeout prefixState := by
  simp [cfg, target, caller, callee, prefixState, enteredState, calleeState, callerState,
    GIR.runModule, GIR.initGlobals, GIR.callFn, GIR.lookupFn, GIR.enterFn, GIR.exec,
    GIR.execOp, GIR.execPure, GIR.execEff, GIR.enterBlock, GIR.bindParams, GIR.getVal,
    GIR.getCell, GIR.setCell, GIR.slotRoot, mapList, freshAct, freshScope, bindRoot,
    Store.introduce, bind_apply, pure_apply, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem_insert, expectBool, timeout, M.stop, maxCallDepth, St.initial, Store.empty]
  <;> rfl

theorem accepted_partial_parameter_cursor :
    ∃ source : BlockSource ⟨.release, TypedExpressionChecks.sourceModule⟩
        ⟨TypedExpressionChecks.boolCallee.vars, 1, [], 2⟩
        [(0, .bool true), (1, .bool false)] TypedExpressionChecks.boolCallee.body calleeState,
      Nonempty (ParameterPrefixCursor source 1) ∧
      prefixState = { calleeState with nextScope := calleeState.nextScope + 1, store := preStore 1 calleeState.nextScope [(0, .bool true)] calleeState.store } := by
  obtain ⟨context, implementation, contextAt, implementationAt, source, typing, roots, _, _⟩ :=
    (TypedExpressionChecks.callSource .release).calleeAfterArgs (after := TypedExpressionChecks.enteredState) 2 [.bool true, .bool false] (by cbv)
  have contextEq : context = ⟨1, "bools", [], [], []⟩ := by
    simpa [TypedExpressionChecks.sourceModule] using (Option.some.inj contextAt).symm
  subst context
  have implementationEq : implementation = TypedExpressionChecks.boolCallee := by
    simpa [TypedExpressionChecks.sourceModule] using (Option.some.inj implementationAt).symm
  subst implementation
  refine ⟨source, source.parameterPrefix 1, ?_⟩
  rfl

theorem accepted_partial_call_retains_caller {map : RetainedSsaMap}
    {world : World} {env : Env} {frame : GIR.Frame} {point : Pt}
    (realized : map.Realizes TypedExpressionChecks.sourceModule world env
      ⟨point, frame, callerState⟩) :
    map.Realizes TypedExpressionChecks.sourceModule world env ⟨point, frame, prefixState⟩ := by
  obtain ⟨source, ⟨cursor⟩, stateEq⟩ := accepted_partial_parameter_cursor
  rw [stateEq]
  exact cursor.retained realized


end Goose.Lower.DemandParameterPrefixChecks

import Goose.Lower.TypedExpressionChecks
import Goose.Proofs.Fuel

namespace Goose.Lower.DemandStateReflectionChecks

open Goose.Core Goose.GIR Goose.Proofs.Fuel

def caller : GIR.Func :=
  { name := "", params := [], results := [], slots := #[], scopes := #[none],
    blocks := #[⟨[], [.eff (.enter 0), .def 0 (.constBool true), .def 1 (.boolNot 0),
      .def 2 (.constBool true), .def 3 (.constBool false), .def 4 (.call 1 [2, 3] (some 0)),
      .eff (.leave 0), .term (.ret [] none)]⟩], roots := { slots := some #[] },
    summary := .unknown, org := none }

def callee : GIR.Func :=
  { name := "bools", params := [.bool, .bool], results := [],
    slots := #[⟨.bool, .immutable, 0, 0⟩, ⟨.bool, .immutable, 0, 1⟩], scopes := #[none],
    blocks := #[⟨[(0, .data .bool), (1, .data .bool)], [.eff (.enter 0),
      .eff (.slotInit 0 0 (some 0)), .eff (.slotInit 1 1 (some 0)), .eff (.leave 0),
      .term (.ret [] none)]⟩], roots := { slots := some #[] }, summary := .unknown,
    org := some 0 }

def target : GIR.Module :=
  { files := #["typed.goose"], globals := #[], funcs := #[caller, callee], entry := 0,
    origins := #[⟨0, 1, "expr"⟩] }

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem actual_lowered : lower TypedExpressionChecks.sourceModule = target := by cbv

private def oneParameterOnly (state : St) : Bool :=
  state.store.roots[RootInst.local 1 1 0]?.isSome &&
    !state.store.roots[RootInst.local 1 1 1]?.isSome

private def resultState (result : Res Unit) : St :=
  match result with
  | .ok _ after => after
  | .stop _ after => after

private def sourceNoPartial (fuel : Nat) : Bool :=
  match Core.runModule fuel ⟨.release, TypedExpressionChecks.sourceModule⟩ St.initial with
  | .stop .timeout after => !oneParameterOnly after
  | _ => true

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
private theorem source_completed :
    ∃ after, Core.runModule 24 ⟨.release, TypedExpressionChecks.sourceModule⟩ St.initial = .ok () after := by
  refine ⟨resultState (Core.runModule 24 ⟨.release, TypedExpressionChecks.sourceModule⟩ St.initial), ?_⟩
  cbv

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
private theorem finite_source_cuts : (List.range 24).all sourceNoPartial = true := by
  cbv

theorem source_has_no_half_bound_parameter_state (fuel : Nat) : sourceNoPartial fuel = true := by
  by_cases enough : 24 ≤ fuel
  · obtain ⟨after, done⟩ := source_completed
    have monotone := MonoM.runModule 24 fuel enough ⟨.release, TypedExpressionChecks.sourceModule⟩ St.initial
    have completed := monotone.1 () after done
    simp only [sourceNoPartial, completed]
  · exact List.all_eq_true.mp finite_source_cuts fuel (List.mem_range.mpr (by omega))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem actual_target_half_bound_parameters :
    ∃ after, GIR.runModule 13 ⟨.release, lower TypedExpressionChecks.sourceModule⟩ St.initial =
      .stop .timeout after ∧ oneParameterOnly after = true := by
  refine ⟨resultState (GIR.runModule 13 ⟨.release, lower TypedExpressionChecks.sourceModule⟩ St.initial), ?_, ?_⟩
  all_goals
    simp [actual_lowered, target, caller, callee, resultState, oneParameterOnly, GIR.runModule, GIR.initGlobals, GIR.callFn,
      GIR.lookupFn, GIR.enterFn, GIR.exec, GIR.execOp, GIR.execPure, GIR.execEff,
      GIR.enterBlock, GIR.bindParams, GIR.getVal, GIR.getCell, GIR.setCell, GIR.slotRoot,
      mapList, freshAct, freshScope, bindRoot, Store.introduce, bind_apply, pure_apply,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, expectBool, timeout, M.stop,
      maxCallDepth, St.initial, Store.empty]
    <;> rfl

private def TotalStateReflection : Prop :=
  ∀ fuel result,
    GIR.runModule fuel ⟨.release, lower TypedExpressionChecks.sourceModule⟩ St.initial = result →
    ∃ sourceFuel, Core.runModule sourceFuel ⟨.release, TypedExpressionChecks.sourceModule⟩ St.initial = result

theorem accepted_total_state_reflection_is_false :
    Core.validate TypedExpressionChecks.sourceModule = .ok () ∧ ¬ TotalStateReflection := by
  refine ⟨(TypedExpressionChecks.callSource .release).accepted, ?_⟩
  intro reflection
  obtain ⟨after, target, halfBound⟩ := actual_target_half_bound_parameters
  obtain ⟨fuel, source⟩ := reflection 13 _ target
  have impossible := source_has_no_half_bound_parameter_state fuel
  simp only [sourceNoPartial, source, halfBound, Bool.not_true] at impossible
  cases impossible

end Goose.Lower.DemandStateReflectionChecks

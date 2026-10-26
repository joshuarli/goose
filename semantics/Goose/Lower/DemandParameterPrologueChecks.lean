import Goose.Lower.DemandParameterPrologue
import Goose.Lower.DemandParameterPrefixChecks
import Goose.Lower.TypedCallChecks

namespace Goose.Lower.DemandParameterPrologueChecks

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

private def boolState : St := { St.initial with nextAct := 2, nextScope := 1 }

theorem bool_all_prefixes (count : Nat) (bound : count ≤ 2) :
    ∃ source : BlockSource ⟨.release, TypedExpressionChecks.sourceModule⟩
        ⟨TypedExpressionChecks.boolCallee.vars, 1, [], 2⟩
        [(0, .bool true), (1, .bool false)] TypedExpressionChecks.boolCallee.body boolState,
      Nonempty (ParameterPrefixCursor source count) ∧
      RuntimePoint ⟨.release, lower TypedExpressionChecks.sourceModule⟩ DemandStateReflectionChecks.callee
        (0, 1 + count)
        { (callFrame TypedExpressionChecks.boolCallee 1 2 [.bool true, .bool false]) with scopes := [(0, 1)] }
        { boolState with nextScope := 2, store := preStore 1 1 ([(0, .bool true), (1, .bool false)].take count) boolState.store } := by
  obtain ⟨source, _, _⟩ := DemandParameterPrefixChecks.accepted_partial_parameter_cursor
  have functionEq : lowerContextAt TypedExpressionChecks.sourceModule
      ⟨1, "bools", [], [], []⟩ TypedExpressionChecks.boolCallee = DemandStateReflectionChecks.callee := by cbv
  have entry : RuntimePoint ⟨.release, lower TypedExpressionChecks.sourceModule⟩
      (lowerContextAt TypedExpressionChecks.sourceModule ⟨1, "bools", [], [], []⟩ TypedExpressionChecks.boolCallee)
      (0, 0) (callFrame TypedExpressionChecks.boolCallee 1 2 [.bool true, .bool false]) boolState := by
    rw [functionEq, DemandStateReflectionChecks.actual_lowered]
    exact DemandParameterPrefixChecks.actual_callee_entry
  have prologue := accepted_callee_parameter_prologue (impl := TypedExpressionChecks.boolCallee)
    (values := [.bool true, .bool false]) (state := boolState) source (ctx := ⟨1, "bools", [], [], []⟩)
    (by rfl) entry count bound
  have reached := prologue.2.1
  rw [functionEq] at reached
  exact ⟨source, prologue.1, by simpa [TypedExpressionChecks.boolCallee, Core.Block.scope, boolState] using reached⟩

theorem bool_timeout_matches_parameter_prefix :
    ∃ frame, RuntimePoint ⟨.release, lower TypedExpressionChecks.sourceModule⟩
        DemandStateReflectionChecks.callee (0, 2) frame
        { boolState with nextScope := 2, store := preStore 1 1 [(0, .bool true)] boolState.store } ∧
      GIR.runModule 13 ⟨.release, lower TypedExpressionChecks.sourceModule⟩ St.initial =
        .stop .timeout
          { boolState with nextScope := 2, store := preStore 1 1 [(0, .bool true)] boolState.store } := by
  obtain ⟨source, cursor, reached⟩ := bool_all_prefixes 1 (by decide)
  refine ⟨_, reached, ?_⟩
  rw [DemandStateReflectionChecks.actual_lowered]
  exact DemandParameterPrefixChecks.actual_timeout_prefix

open TypedCallChecks

private def readonlyCfg : GCfg := ⟨.release, lower (readonlyModule .pilot)⟩
private def globalZero : Core.Global := ⟨"flag", .bool, .mutable, .bool true, 0⟩
private def globalOne : Core.Global := ⟨"selected", .bool, .mutable, .call 1 readonlyArguments 0, 0⟩
private def initializerZero : GIR.Func := (lowerGlobal (readonlyModule .pilot) globalZero).init
private def initializerOne : GIR.Func := (lowerGlobal (readonlyModule .pilot) globalOne).init
private def referenceState : St := { readonlyPrefixState with nextAct := 3 }
private def referenceFrame : GIR.Frame :=
  callFrame readonlyCallee 2 1 [.ref ⟨.global 0, []⟩, .bool true]

private theorem initializer_zero_block : initializerZero.blocks[0]? =
    some ⟨[], [.def 0 (.constBool true), .term (.ret [0] (some 0))]⟩ := by cbv

private theorem initialized_global_zero : GIR.initGlobals 4 readonlyCfg [0] St.initial =
    .ok () readonlyPrefixState := by
  have lookup : readonlyCfg.mod.globals[0]? =
      some (lowerGlobal (readonlyModule .pilot) globalZero) := by cbv
  have parameters : initializerZero.params = [] := by cbv
  simp only [GIR.initGlobals, lookupInit, lookup, pure_bind]
  change (GIR.enterFn 4 readonlyCfg 0 initializerZero [] >>= fun value =>
    bindRoot (.global 0) value >>= fun _ => pure ()) St.initial = _
  simp [GIR.enterFn, parameters, enterBlock, initializer_zero_block, bindParams, exec,
    execOp, execPure, getVal, getCell, setCell,
    readonlyPrefixState, St.initial, bindRoot, bind_apply]
  rfl

private theorem initializer_one_block : initializerOne.blocks[0]? =
    some ⟨[], [.def 0 (.globalAddr 0), .def 1 (.refFreeze 0), .def 2 (.constBool true),
      .def 3 (.call 1 [1, 2] (some 0)), .term (.ret [3] (some 0))]⟩ := by cbv

private theorem readonly_caller_point :
    RuntimePoint readonlyCfg initializerOne (0, 3)
      (((⟨1, [], {}, 0⟩ : GIR.Frame).set 0 (.val (.ref ⟨.global 0, []⟩))).set
        1 (.val (.ref ⟨.global 0, []⟩)) |>.set 2 (.val (.bool true)))
      { readonlyPrefixState with nextAct := 2 } := by
  have initial : RuntimePoint readonlyCfg initializerOne (0, 0) ⟨1, [], {}, 0⟩
      { readonlyPrefixState with nextAct := 2 } := by
    apply RuntimePoint.initializer (fuel := 4) (index := 1) (before := readonlyPrefixState)
      (global := lowerGlobal (readonlyModule .pilot) globalOne)
    · decide
    · cbv
    · exact initialized_global_zero
    · cbv
    · refine ⟨rfl, 1, { readonlyPrefixState with nextAct := 2 }, rfl, ?_⟩
      change enterBlock initializerOne _ _ _ _ = _
      simp [enterBlock, initializer_one_block, instsAt, bindParams, pure_apply]
      change _ = (initializerOne.blocks[0]?.map (·.insts)).getD []
      rw [initializer_one_block]
      rfl
  have first := RuntimePoint.step initial (RuntimeStep.define (fuel := 0)
    (result := 0) (op := .globalAddr 0) (by simp [instAt, initializer_one_block]) rfl)
  have second := RuntimePoint.step first (RuntimeStep.define (fuel := 0)
    (result := 1) (value := .val (.ref ⟨.global 0, []⟩))
    (st' := { readonlyPrefixState with nextAct := 2 }) (op := .refFreeze 0)
    (by simp [instAt, initializer_one_block]) (by
      simp [execOp, execPure, getVal, getCell, Frame.set, expectRef, bind_apply, pure_apply]))
  exact RuntimePoint.step second (RuntimeStep.define (fuel := 0)
    (result := 2) (op := .constBool true) (by simp [instAt, initializer_one_block]) rfl)

private theorem readonly_entry :
    RuntimePoint readonlyCfg (lowerContextAt (readonlyModule .pilot) readonlyContext readonlyCallee)
      (0, 0) referenceFrame referenceState := by
  apply RuntimePoint.call readonly_caller_point (callee := 1) (args := [1, 2])
    (result := 3) (origin := some 0) (values := [.ref ⟨.global 0, []⟩, .bool true])
    (readState := { readonlyPrefixState with nextAct := 2 })
  · simp [instAt, initializer_one_block]
  · decide
  · simp [mapList, getVal, getCell, Frame.set, Std.HashMap.getElem_insert, bind_apply, pure_apply]
  · exact lower_func_at (m := readonlyModule .pilot) rfl rfl
  · refine ⟨rfl, 2, referenceState, rfl, ?_⟩
    have block : (lowerContextAt (readonlyModule .pilot) readonlyContext readonlyCallee).blocks[0]? =
        some ⟨[(0, .data (.ref .readOnly .bool)), (1, .data .bool)],
          [.eff (.enter 0), .eff (.slotInit 0 0 (some 0)), .eff (.slotInit 1 1 (some 0)),
            .def 2 (.constBool true), .eff (.leave 0), .term (.ret [2] none)]⟩ := by cbv
    simp only [enterBlock, instsAt, block]
    rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem readonly_all_prefixes (count : Nat) (bound : count ≤ 2) :
    ∃ source : BlockSource ⟨.release, readonlyModule .pilot⟩ ⟨readonlyCallee.vars, 2, [], 1⟩
        [(0, .ref ⟨.global 0, []⟩), (1, .bool true)] readonlyCallee.body referenceState,
      Nonempty (ParameterPrefixCursor source count) ∧
      RuntimePoint readonlyCfg (lowerContextAt (readonlyModule .pilot) readonlyContext readonlyCallee)
        (0, 1 + count) { referenceFrame with scopes := [(0, 0)] }
        { referenceState with nextScope := 1, store := preStore 2 0 ([(0, .ref ⟨.global 0, []⟩), (1, .bool true)].take count) referenceState.store } := by
  have accepted : Core.validate (readonlyModule .pilot) = .ok () := by cbv
  obtain ⟨call, _, _, _, _, _⟩ := acceptedGlobalActivation
    (cfg := ⟨.release, readonlyModule .pilot⟩) (state := readonlyPrefixState) (g := 1)
    (global := globalOne) accepted rfl (readonly_initialized_prefix .pilot .release accepted).invariant
  obtain ⟨context, implementation, contextAt, implementationAt, source, _, _⟩ :=
    call.calleeAfterArgs 3 [.ref ⟨.global 0, []⟩, .bool true] (readonly_arguments_actual .pilot .release)
  have contextEq : context = readonlyContext := by simpa [readonlyModule] using contextAt.symm
  subst context
  have implementationEq : implementation = readonlyCallee := by
    simpa [readonlyModule, readonlyContext] using implementationAt.symm
  subst implementation
  have prologue := accepted_callee_parameter_prologue (impl := readonlyCallee)
    (values := [.ref ⟨.global 0, []⟩, .bool true]) source (ctx := readonlyContext)
    (by rfl) readonly_entry count bound
  exact ⟨source, prologue.1, prologue.2.1⟩


end Goose.Lower.DemandParameterPrologueChecks

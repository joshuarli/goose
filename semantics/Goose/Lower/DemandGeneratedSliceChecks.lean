import Goose.Lower.DemandGeneratedSliceEntry
import Goose.Lower.DemandGeneratedViewValue
import Goose.Lower.LifetimeChecks

namespace Goose.Lower.DemandGeneratedSliceChecks

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Lower

private def boundBlock (number : Int) : Core.Block := .mk 0 [.clear (.global 0) 0] (some (.lit .i64 number))
private def boundExpression (number : Int) : Expr := .blockE (boundBlock number)
private def upper (number : Int) : Bound := .fromEnd (boundExpression number)
private def sliced (number : Int) : Expr := .slice .readOnly (.of (.global 0)) .omitted (upper number) 0
private def valueView (number : Int) : View := .val (sliced number)
private def measuredGlobal (number : Int) : Core.Global := ⟨"measure", .int .i64, .mutable, .len (valueView number), 0⟩
private def implementation : Impl :=
  { name := "main", params := #[], results := #[], vars := #[], body := .mk 0 [] none, summary := .unknown }
private def sourceModule (number : Int) : Core.Module :=
  { files := #["slice.goose"], types := #[],
    globals := #[⟨"owner", .limited (.int .i64) 1, .mutable,
      .arrLit (.limited (.int .i64) 1) [.lit .i64 9], 0⟩, measuredGlobal number],
    impls := #[implementation], contexts := #[⟨0, "main", [], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "expr"⟩], profile := .shrink }
private def function (number : Int) : Func := (lowerGlobal (sourceModule number) (measuredGlobal number)).init
private def environment (number : Int) : LEnv := lowerEnv (sourceModule number) #[] [.int .i64]
private def root (number : Int) : DemandNode := .expression (.len (valueView number))
private def access (number : Int) : AccessEnv := (⟨sourceModule number, initImpl, initContext, []⟩ : PEnv).access
private def sampledAlias : RetainedAlias := ⟨.slice .readOnly (.int .i64), [.global 0], .operand [0, 0, 0]⟩
private def producedAlias : RetainedAlias := ⟨.slice .readOnly (.int .i64), [.global 0], .operand [0]⟩
private def required : RetainedSsaMap := ⟨[], [(1, sampledAlias)]⟩
private def empty : RetainedSsaMap := ⟨[], []⟩

#guard [0, -1].all fun number =>
  match Core.validate (sourceModule number) with | .ok () => true | .error _ => false

private theorem rootOccurrence (number : Int) :
    GeneratedDemandOccurrence (sourceModule number) (function number) (environment number) (root number) []
      (.expression (.len (valueView number))) startLS := .globalRoot (globalId := 1) (by rfl)
private theorem viewOccurrence (number : Int) :
    GeneratedDemandOccurrence (sourceModule number) (function number) (environment number) (root number) [0]
      (.view (valueView number)) startLS := .first (rootOccurrence number) (.expressionView rfl)
private theorem sliceOccurrence (number : Int) :
    GeneratedDemandOccurrence (sourceModule number) (function number) (environment number) (root number) [0, 0]
      (.expression (sliced number)) startLS := .first (viewOccurrence number) (.viewExpression rfl)
private theorem rootRows (number : Int) :
    GeneratedDemandRows (sourceModule number) (access number) (rootOccurrence number) empty :=
  .globalRoot (globalId := 1) (globalAt := by rfl) rfl
private theorem viewRows (number : Int) :
    GeneratedDemandRows (sourceModule number) (access number) (viewOccurrence number) empty :=
  .first (first := .expressionView rfl) (rootRows number)
private theorem sliceRows (number : Int) :
    GeneratedDemandRows (sourceModule number) (access number) (sliceOccurrence number) empty :=
  .first (first := .viewExpression rfl) (viewRows number)
private theorem upperRows (number : Int) :
    GeneratedDemandRows (sourceModule number) (access number) (.sliceUpper (sliceOccurrence number)) required := by
  exact .sliceUpper (aliases := [sampledAlias]) (sliceRows number) (by cbv)

private theorem valueViewExtended (number : Int) :
    ExtT (lowerView (valueView number) (environment number) startLS).2 (function number).blocks := by
  have extended := generated_global_expression_extended (sourceModule number) (measuredGlobal number)
  have lowered : lowerExpr (.len (valueView number)) (environment number) startLS =
      emitDef (.viewLen (lowerView (valueView number) (environment number) startLS).1) (environment number)
        (lowerView (valueView number) (environment number) startLS).2 := by simp only [lowerExpr, bind_run]
  change ExtT (lowerExpr (.len (valueView number)) (environment number) startLS).2 (function number).blocks at extended
  rw [lowered] at extended
  exact extended.of_adv (adv_emitDef rfl)
private theorem sliceExtended (number : Int) :
    ExtT (lowerExpr (sliced number) (environment number) startLS).2 (function number).blocks :=
  generated_view_value_expression_extended (valueViewExtended number)

theorem generated_checked_slice (number : Int) : GeneratedSliceInstruction (sourceModule number) (access number)
    (function number) required ⟨[0, 0, 2], .bound, .exit⟩ (0, 7)
      (.def 4 (.viewSlice .readOnly 1 .omitted (.fromEnd 3) (some 0))) :=
  .checked (sliceOccurrence number) (upperRows number) (by cbv) (sliceExtended number)

theorem generated_view_value (number : Int) : GeneratedViewValueInstruction (sourceModule number) (access number)
    (function number) empty ⟨[0, 0], .expression, .exit⟩ (0, 8) (.def 5 (.sliceView 4)) :=
  .sliceView (viewOccurrence number) (viewRows number) (by cbv) (valueViewExtended number)

theorem actual_produced_view_alias : (access 0).aliasView [0] (valueView 0) = .ok [producedAlias] := by cbv

theorem omitted_sample_rejected : ¬ empty.Covers required := by
  intro covered
  have missing := covered.2 (1, sampledAlias) (by simp [required])
  cases missing

private def context (number : Int) : FnCtx := ⟨⟨.release, lower (sourceModule number)⟩, function number⟩
private def env : Env := ⟨#[], 0, [], 0⟩
private def initialState : St :=
  ⟨Store.empty.introduce (.global 0) (.limited (.int .i64) 1 LifetimeChecks.physicalSlots 1), "", 0, 0⟩
private def enteredState : St := { initialState with nextScope := 1 }
private def clearedState : St :=
  { enteredState with store := ⟨(enteredState.store.roots.erase (.global 0)).insert (.global 0)
    (.limited (.int .i64) 1 LifetimeChecks.physicalSlots 0)⟩ }
private def addressFrame : GIR.Frame := (⟨0, [], {}, 0⟩ : GIR.Frame).set 0 (.val (.ref ⟨.global 0, []⟩))
private def sampled : GIR.Frame := addressFrame.set 1 (.view LifetimeChecks.sampledView)
private def entered : GIR.Frame := { sampled with scopes := [(0, 0)] }
private def addressed : GIR.Frame := entered.set 2 (.val (.ref ⟨.global 0, []⟩))
private def valued (number : Int) : GIR.Frame := addressed.set 3 (.val (.int .i64 number))
private def prefixFrame (number : Int) : GIR.Frame := { valued number with scopes := [] }
private def sliceFrame : GIR.Frame := (prefixFrame 0).set 4 (.val (.slice ⟨.global 0, []⟩ 0 1))
private def viewFrame : GIR.Frame := sliceFrame.set 5 (.view LifetimeChecks.sampledView)
private def operands (number : Int) : SliceOperands .omitted (upper number) :=
  ⟨LifetimeChecks.sampledView, .omitted, .fromEnd (boundExpression number) .i64 number⟩
private def sampledAt (runtime : DemandRuntimePoint) : Prop :=
  runtime.frame.vals[1]? = some (.view LifetimeChecks.sampledView) ∧
    ∃ logicalLength, logicalLength ≤ 1 ∧ runtime.state.store.read LifetimeChecks.sampledView.loc =
      .ok (.limited (.int .i64) 1 LifetimeChecks.physicalSlots logicalLength)

theorem actual_live_snapshot (number : Int) : DemandInstructionStep (context number) 8
    ⟨(0, 1), addressFrame, initialState⟩ ⟨(0, 2), sampled, initialState⟩ := by
  apply DemandInstructionStep.definition (id := 1) (op := .snapshot .owner 0) (by cbv)
  simp [execOp, execPure, addressFrame, getVal, getCell, Frame.set, initialState, Store.introduce,
    Store.empty, Store.read, Val.get?, readLoc, expectRef, expectArray, LifetimeChecks.physicalSlots,
    LifetimeChecks.sampledView, bind_apply, pure_apply]

theorem actual_prefix_evaluated (number : Int) : (operands number).PrefixEvaluated (.of (.global 0)) 6
    ⟨.release, sourceModule number⟩ env initialState clearedState := by
  exact ⟨initialState, initialState, by cbv, rfl, by cbv⟩

theorem actual_bound_clear_decreases_length (number : Int) :
    enteredState.store.read LifetimeChecks.sampledView.loc =
      .ok (.limited (.int .i64) 1 LifetimeChecks.physicalSlots 1) ∧
    execEff (function number) addressed (.clear 2 (some 0)) enteredState = .ok addressed clearedState ∧
    clearedState.store.read LifetimeChecks.sampledView.loc =
      .ok (.limited (.int .i64) 1 LifetimeChecks.physicalSlots 0) := by
  exact ⟨by cbv, by cbv, by cbv⟩

private theorem prefixTraversal (number : Int) : DemandTraversal (context number) sampledAt 5 7
    ⟨(0, 2), sampled, initialState⟩ ⟨(0, 7), prefixFrame number, clearedState⟩ := by
  refine .next (by refine ⟨?_, 1, by decide, ?_⟩ <;> cbv)
    (.effect (effect := .enter 0) (next := entered) (after := enteredState) (by cbv) (by rfl)) ?_
  refine .next (by refine ⟨?_, 1, by decide, ?_⟩ <;> cbv)
    (.definition (id := 2) (op := .globalAddr 0) (by cbv) (by rfl)) ?_
  refine .next (by refine ⟨?_, 1, by decide, ?_⟩ <;> cbv)
    (.effect (effect := .clear 2 (some 0)) (next := addressed) (after := clearedState)
      (by cbv) (actual_bound_clear_decreases_length number).2.1) ?_
  refine .next (by refine ⟨?_, 0, by decide, ?_⟩ <;> cbv)
    (.definition (id := 3) (op := .constInt .i64 number) (by cbv) (by rfl)) ?_
  refine .next (by refine ⟨?_, 0, by decide, ?_⟩ <;> cbv)
    (.effect (effect := .leave 0) (next := prefixFrame number) (after := clearedState) (by cbv) (by cbv))
    (.done 2 (by refine ⟨?_, 0, by decide, ?_⟩ <;> cbv))

theorem successful_slice_source : evalExpr 8 ⟨.release, sourceModule 0⟩ env (sliced 0) initialState =
    .ok (.slice ⟨.global 0, []⟩ 0 1) clearedState := by
  exact (operands 0).source_decompose .readOnly (.of (.global 0)) 0 (actual_prefix_evaluated 0)

theorem slice_oob_source_preserves_bound_clear : evalExpr 8 ⟨.release, sourceModule (-1)⟩ env (sliced (-1)) initialState =
    .stop (.abort .sliceOob 0) clearedState := by
  exact (operands (-1)).source_decompose .readOnly (.of (.global 0)) 0 (actual_prefix_evaluated (-1))

private theorem physical_sample {module : Core.Module} (world : World) (sourceEnv : Env)
    {store : Store} {frame : GIR.Frame} {id : ValueId} (path : List Nat)
    (cell : frame.vals[id]? = some (.view LifetimeChecks.sampledView))
    (physical : ∃ logicalLength, logicalLength ≤ 1 ∧ store.read LifetimeChecks.sampledView.loc =
      .ok (.limited (.int .i64) 1 LifetimeChecks.physicalSlots logicalLength)) :
    RunAliasAt module world sourceEnv store frame id ⟨.slice .readOnly (.int .i64), [.global 0], .operand path⟩ := by
  apply Or.inl
  refine ⟨LifetimeChecks.sampledView, .readOnly, .int .i64, cell, rfl, ?_⟩
  obtain ⟨logicalLength, bounded, read⟩ := physical
  have flat : Goose.Proofs.Memory.FlatTy (.limited (.int .i64) 1)
      (.limited (.int .i64) 1 LifetimeChecks.physicalSlots logicalLength) := by
    simp only [Goose.Proofs.Memory.FlatTy, bounded, true_and]
    refine ⟨by simpa [LifetimeChecks.physicalSlots] using bounded, ?_⟩
    intro i value found
    cases i with
    | zero => simp [LifetimeChecks.physicalSlots] at found; subst value; rfl
    | succ i => simp [LifetimeChecks.physicalSlots] at found
  constructor
  · refine ⟨LifetimeChecks.sampledView.loc, 0, 1, rfl, rfl, ?_⟩
    exact ⟨.limited (.int .i64) 1 LifetimeChecks.physicalSlots logicalLength,
      LifetimeChecks.physicalSlots, read, rfl, by decide, Or.inr (Or.inr (Or.inr ⟨1, flat⟩))⟩
  · intro root target
    change LifetimeChecks.sampledView.loc.root = root at target
    exact ⟨.global 0, by simp, target.symm⟩

private theorem sampled_rows_realize {module : Core.Module} (world : World) (sourceEnv : Env)
    {runtime : DemandRuntimePoint} (valid : sampledAt runtime) : required.Realizes module world sourceEnv runtime := by
  constructor
  · intro cell member
    cases member
  · intro cell member
    have equal : cell = (1, sampledAlias) := List.mem_singleton.mp member
    subst cell
    exact physical_sample world sourceEnv [0, 0, 0] valid.1 valid.2

private theorem prefixCells (number : Int) :
    ∀ cell ∈ (operands number).cells (.of (.global 0)) (environment number) startLS,
      (prefixFrame number).vals[cell.1]? = some cell.2 := by
  intro cell member
  simp [operands, SliceOperands.cells, SliceBoundOperand.cells] at member
  rcases member with rfl | rfl <;> cbv

private theorem sliceExecution (number : Int) (fuel : Nat) :
    execOp fuel (context number) (prefixFrame number)
        (sliceOperation .readOnly (.of (.global 0)) .omitted (upper number) 0 (environment number) startLS) clearedState =
      match (operands number).compute 0 with
      | .ok value => .ok (.val value) clearedState
      | .error stop => .stop stop clearedState :=
  (operands number).instruction_decompose .readOnly (.of (.global 0)) 0 (prefixCells number) fuel clearedState

private theorem viewValueExecution (fuel : Nat) :
    execOp fuel (context 0) sliceFrame (.sliceView 4) clearedState = .ok (.view LifetimeChecks.sampledView) clearedState := by
  have cell : sliceFrame.vals[4]? = some (.val (.slice ⟨.global 0, []⟩ 0 1)) := Frame.set_get _ _ _
  simp only [execOp, execPure, getVal_of cell, expectSlice, pure_bind, pure_apply]
  rfl

theorem actual_slice_runtime_step : Evidence.RuntimeStep (context 0).cfg (context 0).fn (0, 7) (prefixFrame 0) clearedState
    (0, 8) sliceFrame clearedState := by
  exact .define (fuel := 1) (generated_checked_slice 0).instruction (sliceExecution 0 1)

theorem actual_view_value_runtime_step : Evidence.RuntimeStep (context 0).cfg (context 0).fn (0, 8) sliceFrame clearedState
    (0, 9) viewFrame clearedState := by
  exact .define (fuel := 0) (generated_view_value 0).instruction (viewValueExecution 0)

theorem value_view_source_retains_saved_extent : evalView 9 ⟨.release, sourceModule 0⟩ env (valueView 0) initialState =
    .ok LifetimeChecks.sampledView clearedState := by
  exact (view_value_runtime_reflection successful_slice_source (Frame.set_get _ _ _) (viewValueExecution 0)).2.2

theorem measured_source_retains_saved_extent : evalExpr 10 ⟨.release, sourceModule 0⟩ env (.len (valueView 0)) initialState =
    .ok (.int .i64 1) clearedState := by
  simp only [evalExpr, bind_apply, value_view_source_retains_saved_extent, pure_apply]
  rfl

theorem actual_slice_value_traversal : DemandTraversal (context 0) sampledAt 7 7
    ⟨(0, 2), sampled, initialState⟩ ⟨(0, 9), viewFrame, clearedState⟩ := by
  have suffix : DemandTraversal (context 0) sampledAt 2 2
      ⟨(0, 7), prefixFrame 0, clearedState⟩ ⟨(0, 9), viewFrame, clearedState⟩ := by
    refine .next (by refine ⟨?_, 0, by decide, ?_⟩ <;> cbv)
      (.definition (generated_checked_slice 0).instruction (sliceExecution 0 1)) ?_
    refine .next (by refine ⟨?_, 0, by decide, ?_⟩ <;> cbv)
      (.definition (generated_view_value 0).instruction (viewValueExecution 0))
      (.done 0 (by refine ⟨?_, 0, by decide, ?_⟩ <;> cbv))
  exact (prefixTraversal 0).append suffix

theorem actual_slice_oob_stop : DemandInstructionStop (context (-1)) 2 ⟨(0, 7), prefixFrame (-1), clearedState⟩
    (.abort .sliceOob 0) clearedState :=
  .definition (generated_checked_slice (-1)).instruction (sliceExecution (-1) 1)

theorem actual_slice_oob_traversal : DemandStoppedTraversal (context (-1)) sampledAt 5 7
    ⟨(0, 2), sampled, initialState⟩ (.abort .sliceOob 0) clearedState :=
  ⟨⟨(0, 7), prefixFrame (-1), clearedState⟩, prefixTraversal (-1), actual_slice_oob_stop⟩

theorem success_runtime_prefix_rows (world : World) (sourceEnv : Env) {taken : Nat} {runtime : DemandRuntimePoint}
    (bounded : taken ≤ 7) (steps : DemandRuntimePrefix (context 0) taken ⟨(0, 2), sampled, initialState⟩ runtime) :
    required.Realizes (sourceModule 0) world sourceEnv runtime :=
  sampled_rows_realize world sourceEnv (actual_slice_value_traversal.runtimePrefix_invariant bounded steps)

theorem abort_runtime_prefix_rows (world : World) (sourceEnv : Env) {taken : Nat} {runtime : DemandRuntimePoint}
    (steps : DemandRuntimePrefix (context (-1)) taken ⟨(0, 2), sampled, initialState⟩ runtime) :
    required.Realizes (sourceModule (-1)) world sourceEnv runtime :=
  sampled_rows_realize world sourceEnv (actual_slice_oob_traversal.runtimePrefix_invariant (by intro impossible; cases impossible) steps)

theorem abort_exec_preserves_bound_effects : runAt (context (-1)) (0, 2) sampled 7 initialState =
    .stop (.abort .sliceOob 0) clearedState := actual_slice_oob_traversal.runAt

theorem produced_view_run_realized (world : World) (sourceEnv : Env) :
    (required.addRuns 5 [producedAlias]).Realizes (sourceModule 0) world sourceEnv ⟨(0, 9), viewFrame, clearedState⟩ := by
  have physical : ∃ logicalLength, logicalLength ≤ 1 ∧ clearedState.store.read LifetimeChecks.sampledView.loc =
      .ok (.limited (.int .i64) 1 LifetimeChecks.physicalSlots logicalLength) := ⟨0, by decide, by cbv⟩
  apply RetainedSsaMap.addRuns_realizes
    (sampled_rows_realize world sourceEnv (show sampledAt ⟨(0, 9), viewFrame, clearedState⟩ from ⟨by cbv, physical⟩))
  intro alias member
  have equal : alias = producedAlias := List.mem_singleton.mp member
  subst alias
  exact physical_sample world sourceEnv [0] (Frame.set_get _ _ _) physical

theorem physically_removed_sample_rejected (world : World) (sourceEnv : Env) :
    ¬ required.Realizes (sourceModule 0) world sourceEnv ⟨(0, 7), prefixFrame 0, LifetimeChecks.removedSample⟩ := by
  intro realized
  obtain ⟨values, read⟩ := (realized.2 (1, sampledAlias) (by simp [required])).read_safe
  have faulted : (getView (prefixFrame 0) 1 >>= readRun) LifetimeChecks.removedSample =
      .stop (.fault .pathRange) LifetimeChecks.removedSample := by cbv
  rw [faulted] at read
  cases read

end Goose.Lower.DemandGeneratedSliceChecks

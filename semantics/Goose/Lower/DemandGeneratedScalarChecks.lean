import Goose.Lower.DemandGeneratedScalarSteps
import Goose.Lower.LifetimeChecks

namespace Goose.Lower.DemandGeneratedScalarChecks

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Lower

private def rightBlock : Core.Block := .mk 0 [.clear (.global 0) 0] (some (.lit .i64 0))
private def left : Expr := .lit .i64 0
private def right : Expr := .blockE rightBlock
private def scalar (operation : BinOp) : Expr := .bin operation left right 0
private def form (operation : BinOp) : ScalarExpression (scalar operation) := .binary operation left right 0
private def location (operation : BinOp) : Place := .elem (.of (.global 0)) (scalar operation) 0
private def indexedGlobal (operation : BinOp) : Core.Global := ⟨"indexed", .int .i64, .mutable, .read (location operation), 0⟩
private def implementation : Impl :=
  { name := "main", params := #[], results := #[], vars := #[], body := .mk 0 [] none, summary := .unknown }
private def sourceModule (operation : BinOp) : Core.Module :=
  { files := #["scalar.goose"], types := #[],
    globals := #[⟨"owner", .limited (.int .i64) 1, .mutable,
      .arrLit (.limited (.int .i64) 1) [.lit .i64 9], 0⟩, indexedGlobal operation],
    impls := #[implementation], contexts := #[⟨0, "main", [], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "expr"⟩], profile := .shrink }
private def function (operation : BinOp) : Func := (lowerGlobal (sourceModule operation) (indexedGlobal operation)).init
private def environment (operation : BinOp) : LEnv := lowerEnv (sourceModule operation) #[] [.int .i64]
private def access (operation : BinOp) : AccessEnv := (⟨sourceModule operation, initImpl, initContext, []⟩ : PEnv).access
private def root (operation : BinOp) : DemandNode := .expression (.read (location operation))
private def before (operation : BinOp) : LS := (lowerView (.of (.global 0)) (environment operation) startLS).2
private def sampledAlias : RetainedAlias := ⟨.slice .readOnly (.int .i64), [.global 0], .operand [0, 0]⟩
private def required : RetainedSsaMap := ⟨[], [(1, sampledAlias)]⟩
private def empty : RetainedSsaMap := ⟨[], []⟩

#guard [BinOp.add, .div].all fun operation =>
  match Core.validate (sourceModule operation) with | .ok () => true | .error _ => false

private theorem rootOccurrence (operation : BinOp) :
    GeneratedDemandOccurrence (sourceModule operation) (function operation) (environment operation) (root operation) []
      (.expression (.read (location operation))) startLS := .globalRoot (globalId := 1) (by rfl)
private theorem placeOccurrence (operation : BinOp) :
    GeneratedDemandOccurrence (sourceModule operation) (function operation) (environment operation) (root operation) [0]
      (.place (location operation)) startLS := .first (rootOccurrence operation) (.expressionPlace rfl)
private theorem scalarOccurrence (operation : BinOp) :
    GeneratedDemandOccurrence (sourceModule operation) (function operation) (environment operation) (root operation) [0, 1]
      (.expression (scalar operation)) (before operation) := .index (placeOccurrence operation)
private theorem rootRows (operation : BinOp) :
    GeneratedDemandRows (sourceModule operation) (access operation) (rootOccurrence operation) empty :=
  .globalRoot (globalId := 1) (globalAt := by rfl) rfl
private theorem scalarRows (operation : BinOp) :
    GeneratedDemandRows (sourceModule operation) (access operation) (scalarOccurrence operation) required := by
  exact .index (aliases := [sampledAlias]) (.first (first := .expressionPlace rfl) (rootRows operation)) (by cbv)

theorem generated_scalar_site (operation : BinOp) :
    GeneratedScalarSite (form operation) (sourceModule operation) (access operation) (function operation)
      (environment operation) (root operation) [0, 1] (before operation) required (0, 8) := by
  refine ⟨scalarOccurrence operation, ?_, by cbv, ?_⟩
  · change GeneratedDemandRows _ _ (.binaryRight (scalarOccurrence operation)) required
    exact .binaryRight (aliases := []) (scalarRows operation) (by cbv)
  · exact generated_index_expression_extended (generated_read_place_extended
      (generated_global_expression_extended (sourceModule operation) (indexedGlobal operation)))

theorem omitted_sample_rejected : ¬ empty.Covers required := by
  intro covered
  have missing := covered.2 (1, sampledAlias) (by simp [required])
  cases missing

private def context (operation : BinOp) : FnCtx := ⟨⟨.release, lower (sourceModule operation)⟩, function operation⟩
private def env : Env := ⟨#[], 0, [], 0⟩
private def initialState : St :=
  ⟨Store.empty.introduce (.global 0) (.limited (.int .i64) 1 LifetimeChecks.physicalSlots 1), "", 0, 0⟩
private def enteredState : St := { initialState with nextScope := 1 }
private def clearedState : St :=
  { enteredState with store := ⟨(enteredState.store.roots.erase (.global 0)).insert (.global 0)
    (.limited (.int .i64) 1 LifetimeChecks.physicalSlots 0)⟩ }
private def addressFrame : GIR.Frame := (⟨0, [], {}, 0⟩ : GIR.Frame).set 0 (.val (.ref ⟨.global 0, []⟩))
private def sampled : GIR.Frame := addressFrame.set 1 (.view LifetimeChecks.sampledView)
private def leftFrame : GIR.Frame := sampled.set 2 (.val (.int .i64 0))
private def entered : GIR.Frame := { leftFrame with scopes := [(0, 0)] }
private def addressed : GIR.Frame := entered.set 3 (.val (.ref ⟨.global 0, []⟩))
private def valued : GIR.Frame := addressed.set 4 (.val (.int .i64 0))
private def prefixFrame : GIR.Frame := { valued with scopes := [] }
private def resultFrame : GIR.Frame := prefixFrame.set 5 (.val (.int .i64 0))
private def sampledAt (runtime : DemandRuntimePoint) : Prop :=
  runtime.frame.vals[1]? = some (.view LifetimeChecks.sampledView) ∧
    ∃ logicalLength, logicalLength ≤ 1 ∧ runtime.state.store.read LifetimeChecks.sampledView.loc =
      .ok (.limited (.int .i64) 1 LifetimeChecks.physicalSlots logicalLength)

theorem actual_live_snapshot (operation : BinOp) : DemandInstructionStep (context operation) 8
    ⟨(0, 1), addressFrame, initialState⟩ ⟨(0, 2), sampled, initialState⟩ := by
  apply DemandInstructionStep.definition (id := 1) (op := .snapshot .owner 0) (by cbv)
  simp [execOp, execPure, addressFrame, getVal, getCell, Frame.set, initialState, Store.introduce,
    Store.empty, Store.read, Val.get?, readLoc, expectRef, expectArray, LifetimeChecks.physicalSlots,
    LifetimeChecks.sampledView, bind_apply, pure_apply]

theorem actual_prefix_evaluated (operation : BinOp) :
    (form operation).PrefixEvaluated (.i64, 0, 0) 6 ⟨.release, sourceModule operation⟩ env initialState clearedState := by
  exact ⟨initialState, by cbv, by cbv⟩

theorem actual_rhs_clear_decreases_length (operation : BinOp) :
    enteredState.store.read LifetimeChecks.sampledView.loc =
      .ok (.limited (.int .i64) 1 LifetimeChecks.physicalSlots 1) ∧
    execEff (function operation) addressed (.clear 3 (some 0)) enteredState = .ok addressed clearedState ∧
    clearedState.store.read LifetimeChecks.sampledView.loc =
      .ok (.limited (.int .i64) 1 LifetimeChecks.physicalSlots 0) := by
  exact ⟨by cbv, by cbv, by cbv⟩

private theorem prefixTraversal (operation : BinOp) : DemandTraversal (context operation) sampledAt 6 7
    ⟨(0, 2), sampled, initialState⟩ ⟨(0, 8), prefixFrame, clearedState⟩ := by
  refine .next (by refine ⟨?_, 1, by decide, ?_⟩ <;> cbv)
    (.definition (id := 2) (op := .constInt .i64 0) (by cbv) (by rfl)) ?_
  refine .next (by refine ⟨?_, 1, by decide, ?_⟩ <;> cbv)
    (.effect (effect := .enter 0) (next := entered) (after := enteredState) (by cbv) (by rfl)) ?_
  refine .next (by refine ⟨?_, 1, by decide, ?_⟩ <;> cbv)
    (.definition (id := 3) (op := .globalAddr 0) (by cbv) (by rfl)) ?_
  refine .next (by refine ⟨?_, 1, by decide, ?_⟩ <;> cbv)
    (.effect (effect := .clear 3 (some 0)) (next := addressed) (after := clearedState)
      (by cbv) (actual_rhs_clear_decreases_length operation).2.1) ?_
  refine .next (by refine ⟨?_, 0, by decide, ?_⟩ <;> cbv)
    (.definition (id := 4) (op := .constInt .i64 0) (by cbv) (by rfl)) ?_
  refine .next (by refine ⟨?_, 0, by decide, ?_⟩ <;> cbv)
    (.effect (effect := .leave 0) (next := prefixFrame) (after := clearedState) (by cbv) (by cbv))
    (.done 1 (by refine ⟨?_, 0, by decide, ?_⟩ <;> cbv))

theorem numeric_success_source_preserves_rhs_clear :
    evalExpr 7 ⟨.release, sourceModule .add⟩ env (scalar .add) initialState = .ok (.int .i64 0) clearedState := by
  rw [(form .add).source_decompose (.i64, 0, 0) (actual_prefix_evaluated .add)]
  cbv

theorem numeric_abort_source_preserves_rhs_clear :
    evalExpr 7 ⟨.release, sourceModule .div⟩ env (scalar .div) initialState =
      .stop (.abort (AbortKind.ofNum .divZero) 0) clearedState := by
  rw [(form .div).source_decompose (.i64, 0, 0) (actual_prefix_evaluated .div)]
  cbv

private theorem sampled_rows_realize {module : Core.Module} (world : World) (env : Env)
    {runtime : DemandRuntimePoint} (valid : sampledAt runtime) : required.Realizes module world env runtime := by
  constructor
  · intro cell member
    cases member
  · intro cell member
    have equal : cell = (1, sampledAlias) := List.mem_singleton.mp member
    subst cell
    apply Or.inl
    refine ⟨LifetimeChecks.sampledView, .readOnly, .int .i64, valid.1, rfl, ?_⟩
    obtain ⟨logicalLength, bounded, read⟩ := valid.2
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
      exact ⟨.global 0, by simp [sampledAlias], target.symm⟩

private theorem prefixCells (operation : BinOp) :
    ∀ cell ∈ (form operation).cells (environment operation) (before operation) (.i64, 0, 0),
      prefixFrame.vals[cell.1]? = some cell.2 := by
  intro cell member
  simp [form, ScalarExpression.cells] at member
  rcases member with rfl | rfl <;> cbv

private theorem numericExecution (operation : BinOp) (fuel : Nat) :
    execOp fuel (context operation) prefixFrame ((form operation).operation (environment operation) (before operation)) clearedState =
      match (form operation).compute .release (.i64, 0, 0) with
      | .ok value => .ok (.val value) clearedState
      | .error stop => .stop stop clearedState :=
  (form operation).instruction_decompose (.i64, 0, 0) rfl (prefixCells operation) fuel clearedState

theorem actual_numeric_runtime_step : Evidence.RuntimeStep (context .add).cfg (context .add).fn
    (0, 8) prefixFrame clearedState (0, 9) resultFrame clearedState := by
  apply Evidence.RuntimeStep.define (fuel := 0) (result := 5) (op := .bin .add .i64 2 4 (some 0))
    (generated_scalar_site .add).instruction
  exact numericExecution .add 0

theorem actual_numeric_traversal : DemandTraversal (context .add) sampledAt 7 7
    ⟨(0, 2), sampled, initialState⟩ ⟨(0, 9), resultFrame, clearedState⟩ := by
  have suffix : DemandTraversal (context .add) sampledAt 1 1
      ⟨(0, 8), prefixFrame, clearedState⟩ ⟨(0, 9), resultFrame, clearedState⟩ := by
    refine .next (by refine ⟨?_, 0, by decide, ?_⟩ <;> cbv)
      (.definition (generated_scalar_site .add).instruction (numericExecution .add 0))
      (.done 0 (by refine ⟨?_, 0, by decide, ?_⟩ <;> cbv))
  exact (prefixTraversal .add).append suffix

theorem actual_numeric_abort : DemandInstructionStop (context .div) 1 ⟨(0, 8), prefixFrame, clearedState⟩
    (.abort (AbortKind.ofNum .divZero) 0) clearedState := by
  exact .definition (generated_scalar_site .div).instruction (numericExecution .div 0)

theorem actual_abort_traversal : DemandStoppedTraversal (context .div) sampledAt 6 7
    ⟨(0, 2), sampled, initialState⟩ (.abort (AbortKind.ofNum .divZero) 0) clearedState :=
  ⟨⟨(0, 8), prefixFrame, clearedState⟩, prefixTraversal .div, actual_numeric_abort⟩

theorem success_runtime_prefix_rows (world : World) (sourceEnv : Env)
    {taken : Nat} {runtime : DemandRuntimePoint} (bounded : taken ≤ 7)
    (steps : DemandRuntimePrefix (context .add) taken ⟨(0, 2), sampled, initialState⟩ runtime) :
    required.Realizes (sourceModule .add) world sourceEnv runtime :=
  sampled_rows_realize world sourceEnv (actual_numeric_traversal.runtimePrefix_invariant bounded steps)

theorem abort_runtime_prefix_rows (world : World) (sourceEnv : Env)
    {taken : Nat} {runtime : DemandRuntimePoint}
    (steps : DemandRuntimePrefix (context .div) taken ⟨(0, 2), sampled, initialState⟩ runtime) :
    required.Realizes (sourceModule .div) world sourceEnv runtime :=
  sampled_rows_realize world sourceEnv (actual_abort_traversal.runtimePrefix_invariant (by intro impossible; cases impossible) steps)

theorem abort_exec_preserves_rhs_effects :
    runAt (context .div) (0, 2) sampled 7 initialState = .stop (.abort (AbortKind.ofNum .divZero) 0) clearedState :=
  actual_abort_traversal.runAt

theorem physically_removed_sample_rejected (world : World) (sourceEnv : Env) :
    ¬ required.Realizes (sourceModule .add) world sourceEnv ⟨(0, 8), prefixFrame, LifetimeChecks.removedSample⟩ := by
  intro realized
  obtain ⟨values, read⟩ := (realized.2 (1, sampledAlias) (by simp [required])).read_safe
  have faulted : (getView prefixFrame 1 >>= readRun) LifetimeChecks.removedSample =
      .stop (.fault .pathRange) LifetimeChecks.removedSample := by cbv
  rw [faulted] at read
  cases read

end Goose.Lower.DemandGeneratedScalarChecks

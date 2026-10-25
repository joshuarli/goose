import Goose.Lower.DemandGeneratedShortCircuit
import Goose.Lower.LifetimeChecks

namespace Goose.Lower.DemandGeneratedShortCircuitChecks

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Lower

private def rhsBlock : Core.Block := .mk 0 [.clear (.global 0) 0] (some (.bool true))
private def right : Expr := .blockE rhsBlock
private def expression (isAnd leftValue : Bool) : Expr :=
  if isAnd then .and (.bool leftValue) right else .or (.bool leftValue) right
private def indexExpression (isAnd leftValue : Bool) : Expr :=
  .ifE (expression isAnd leftValue) (.mk 1 [] (some (.lit .i64 0))) (.mk 2 [] (some (.lit .i64 0)))
private def location (isAnd leftValue : Bool) : Place :=
  .elem (.of (.global 0)) (indexExpression isAnd leftValue) 0
private def indexedGlobal (isAnd leftValue : Bool) : Core.Global :=
  ⟨"indexed", .int .i64, .mutable, .read (location isAnd leftValue), 0⟩
private def implementation : Impl :=
  { name := "main", params := #[], results := #[], vars := #[], body := .mk 0 [] none, summary := .unknown }
private def sourceModule (isAnd leftValue : Bool) : Core.Module :=
  { files := #["short-circuit.goose"], types := #[],
    globals := #[⟨"owner", .limited (.int .i64) 1, .mutable,
      .arrLit (.limited (.int .i64) 1) [.lit .i64 9], 0⟩, indexedGlobal isAnd leftValue],
    impls := #[implementation], contexts := #[⟨0, "main", [], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "expr"⟩], profile := .shrink }
private def function (isAnd leftValue : Bool) : Func :=
  (lowerGlobal (sourceModule isAnd leftValue) (indexedGlobal isAnd leftValue)).init
private def environment (isAnd leftValue : Bool) : LEnv := lowerEnv (sourceModule isAnd leftValue) #[] [.int .i64]
private def root (isAnd leftValue : Bool) : DemandNode := .expression (.read (location isAnd leftValue))
private def access (isAnd leftValue : Bool) : AccessEnv :=
  (⟨sourceModule isAnd leftValue, initImpl, initContext, []⟩ : PEnv).access
private def empty : RetainedSsaMap := ⟨[], []⟩
private def sampledAlias : RetainedAlias := ⟨.slice .readOnly (.int .i64), [.global 0], .operand [0, 0]⟩
private def required : RetainedSsaMap := ⟨[], [(1, sampledAlias)]⟩
private def indexBefore (isAnd leftValue : Bool) : LS :=
  (lowerView (.of (.global 0)) (environment isAnd leftValue) startLS).2

#guard [false, true].all fun isAnd => [false, true].all fun leftValue =>
  match Core.validate (sourceModule isAnd leftValue) with
  | .ok () => true
  | .error _ => false

private theorem rootOccurrence (isAnd leftValue : Bool) :
    GeneratedDemandOccurrence (sourceModule isAnd leftValue) (function isAnd leftValue)
      (environment isAnd leftValue) (root isAnd leftValue) []
      (.expression (.read (location isAnd leftValue))) startLS :=
  .globalRoot (globalId := 1) (by rfl)
private theorem placeOccurrence (isAnd leftValue : Bool) :
    GeneratedDemandOccurrence (sourceModule isAnd leftValue) (function isAnd leftValue)
      (environment isAnd leftValue) (root isAnd leftValue) [0]
      (.place (location isAnd leftValue)) startLS :=
  GeneratedDemandOccurrence.first (rootOccurrence isAnd leftValue)
    (DemandLoweringAction.FirstChild.expressionPlace rfl)
private theorem indexOccurrence (isAnd leftValue : Bool) :
    GeneratedDemandOccurrence (sourceModule isAnd leftValue) (function isAnd leftValue)
      (environment isAnd leftValue) (root isAnd leftValue) [0, 1]
      (.expression (indexExpression isAnd leftValue)) (indexBefore isAnd leftValue) :=
  GeneratedDemandOccurrence.index (placeOccurrence isAnd leftValue)
private theorem conditionOccurrence (isAnd leftValue : Bool) :
    GeneratedDemandOccurrence (sourceModule isAnd leftValue) (function isAnd leftValue)
      (environment isAnd leftValue) (root isAnd leftValue) [0, 1, 0]
      (.expression (expression isAnd leftValue)) (indexBefore isAnd leftValue) :=
  .first (indexOccurrence isAnd leftValue) (.expression rfl)
private theorem rootRows (isAnd leftValue : Bool) :
    GeneratedDemandRows (sourceModule isAnd leftValue) (access isAnd leftValue)
      (rootOccurrence isAnd leftValue) empty := .globalRoot (globalId := 1) (globalAt := by rfl) rfl
private theorem indexRows (isAnd leftValue : Bool) :
    GeneratedDemandRows (sourceModule isAnd leftValue) (access isAnd leftValue)
      (indexOccurrence isAnd leftValue) required := by
  exact .index (aliases := [sampledAlias]) (.first (first := .expressionPlace rfl) (rootRows isAnd leftValue)) (by cbv)
private theorem conditionRows (isAnd leftValue : Bool) :
    GeneratedDemandRows (sourceModule isAnd leftValue) (access isAnd leftValue)
      (conditionOccurrence isAnd leftValue) required :=
  .first (first := .expression rfl) (indexRows isAnd leftValue)

private theorem conditionExtended (isAnd leftValue : Bool) :
    ExtT (lowerExpr (expression isAnd leftValue) (environment isAnd leftValue)
      (indexBefore isAnd leftValue)).2 (function isAnd leftValue).blocks := by
  have indexExtended := generated_index_expression_extended
    (generated_read_place_extended
      (generated_global_expression_extended (sourceModule isAnd leftValue) (indexedGlobal isAnd leftValue)))
  exact indexExtended.of_adv
    (advB_ifE_core _ _ (advB_lowerBlock none [] true (.mk 1 [] (some (.lit .i64 0))))
      (advB_lowerBlock none [] true (.mk 2 [] (some (.lit .i64 0)))) _ _ _ _ rfl)

private theorem forkExtended (isAnd leftValue : Bool) :
    ExtT (demandShortCircuitFork isAnd (.bool leftValue) (environment isAnd leftValue)
      (indexBefore isAnd leftValue)).2 (function isAnd leftValue).blocks :=
  generated_shortCircuit_fork_extended (right := right) (by cbv) (conditionExtended isAnd leftValue)

private theorem jumpExtended (isAnd leftValue : Bool) :
    ExtT (demandShortCircuitRightJump isAnd (.bool leftValue) right (environment isAnd leftValue)
      (indexBefore isAnd leftValue)) (function isAnd leftValue).blocks :=
  generated_shortCircuit_jump_extended (by cbv) (conditionExtended isAnd leftValue)

theorem generated_fork (isAnd leftValue : Bool) :
    GeneratedShortCircuitSite (sourceModule isAnd leftValue) (access isAnd leftValue)
      (function isAnd leftValue) required ⟨[0, 1, 0, 0], .expression, .exit⟩ (0, 3)
      (.term (scTerm isAnd 2 1 2)) := by
  cases isAnd with
  | false =>
    exact .fork (isAnd := false) (left := .bool leftValue) (right := right)
      (aliases := []) (conditionOccurrence false leftValue) (conditionRows false leftValue)
      (by cbv) (by cbv) (forkExtended false leftValue)
  | true =>
    exact .fork (isAnd := true) (left := .bool leftValue) (right := right)
      (aliases := []) (conditionOccurrence true leftValue) (conditionRows true leftValue)
      (by cbv) (by cbv) (forkExtended true leftValue)

theorem generated_right_jump (isAnd leftValue : Bool) :
    GeneratedShortCircuitSite (sourceModule isAnd leftValue) (access isAnd leftValue)
      (function isAnd leftValue) required ⟨[0, 1, 0, 1], .expression, .exit⟩ (1, 5)
      (.term (.br 2 [5])) := by
  cases isAnd with
  | false =>
    exact .rightJump (isAnd := false) (left := .bool leftValue) (right := right)
      (aliases := []) (conditionOccurrence false leftValue) (conditionRows false leftValue)
      (by cbv) (by cbv) (by cbv) (jumpExtended false leftValue)
  | true =>
    exact .rightJump (isAnd := true) (left := .bool leftValue) (right := right)
      (aliases := []) (conditionOccurrence true leftValue) (conditionRows true leftValue)
      (by cbv) (by cbv) (by cbv) (jumpExtended true leftValue)

theorem empty_map_cannot_cover_fork_or_rhs : ¬ empty.Covers required := by
  intro coverage
  have missing := coverage.2 (1, sampledAlias) (by simp [required])
  cases missing


private def context : FnCtx := ⟨⟨.release, lower (sourceModule true true)⟩, function true true⟩
private def sampled : GIR.Frame :=
  (((⟨0, [], {}, 0⟩ : GIR.Frame).set 0 (.val (.ref ⟨.global 0, []⟩))).set 1 (.view LifetimeChecks.sampledView))
private def conditioned : GIR.Frame := sampled.set 2 (.val (.bool true))
private def entered : GIR.Frame := { conditioned with scopes := [(0, 0)] }
private def addressed : GIR.Frame := entered.set 4 (.val (.ref ⟨.global 0, []⟩))
private def valued : GIR.Frame := addressed.set 5 (.val (.bool true))
private def leftScope : GIR.Frame := { valued with scopes := [] }
private def joined : GIR.Frame := leftScope.set 3 (.val (.bool true))
private def initialState : St := ⟨LifetimeChecks.clearedOwner, "", 0, 0⟩
private def enteredState : St := { initialState with nextScope := 1 }
private def clearedState : St :=
  { enteredState with store := ⟨(enteredState.store.roots.erase (.global 0)).insert (.global 0)
    (.limited (.int .i64) 1 LifetimeChecks.physicalSlots 0)⟩ }
private def sampledAt (runtime : DemandRuntimePoint) : Prop :=
  runtime.frame.vals[1]? = some (.view LifetimeChecks.sampledView) ∧
    runtime.state.store.read LifetimeChecks.sampledView.loc =
      .ok (.limited (.int .i64) 1 LifetimeChecks.physicalSlots 0)

private theorem sampled_rows_realize (world : World) (env : Env) {runtime : DemandRuntimePoint}
    (valid : sampledAt runtime) : required.Realizes (sourceModule true true) world env runtime := by
  constructor
  · intro cell member
    cases member
  · intro cell member
    have equal : cell = (1, sampledAlias) := List.mem_singleton.mp member
    subst cell
    apply Or.inl
    refine ⟨LifetimeChecks.sampledView, .readOnly, .int .i64, valid.1, rfl, ?_⟩
    have flat : Goose.Proofs.Memory.FlatTy (.limited (.int .i64) 1)
        (.limited (.int .i64) 1 LifetimeChecks.physicalSlots 0) := by
      simp only [Goose.Proofs.Memory.FlatTy, Nat.zero_le, true_and]
      intro i value found
      cases i with
      | zero => simp [LifetimeChecks.physicalSlots] at found; subst value; rfl
      | succ i => simp [LifetimeChecks.physicalSlots] at found
    constructor
    · refine ⟨LifetimeChecks.sampledView.loc, 0, 1, rfl, rfl, ?_⟩
      exact ⟨.limited (.int .i64) 1 LifetimeChecks.physicalSlots 0,
        LifetimeChecks.physicalSlots, valid.2, rfl, by decide,
        Or.inr (Or.inr (Or.inr ⟨1, flat⟩))⟩
    · intro root target
      change LifetimeChecks.sampledView.loc.root = root at target
      exact ⟨.global 0, by simp [sampledAlias], target.symm⟩

private theorem leftTraversal : DemandTraversal context sampledAt 1 9
    ⟨(0, 2), sampled, initialState⟩ ⟨(0, 3), conditioned, initialState⟩ := by
  refine .next (by cbv) (.definition (id := 2) (op := .constBool true) (by cbv) (by rfl))
    (.done 8 (by cbv))

private theorem rightTraversal : DemandTraversal context sampledAt 5 7
    ⟨(1, 0), conditioned, initialState⟩ ⟨(1, 5), leftScope, clearedState⟩ := by
  refine .next (by cbv) (.effect (effect := .enter 0) (by cbv) (by rfl)) ?_
  refine .next (by cbv) (.definition (id := 4) (op := .globalAddr 0) (by cbv) (by rfl)) ?_
  refine .next (by cbv) (.effect (effect := .clear 4 (some 0)) (by cbv) (by cbv)) ?_
  refine .next (by cbv) (.definition (id := 5) (op := .constBool true) (by cbv) (by rfl)) ?_
  refine .next (by cbv) (.effect (effect := .leave 0) (by cbv) (by cbv)) (.done 2 (by cbv))

private theorem continuationTraversal : DemandTraversal context sampledAt 1 1
    ⟨(2, 0), joined, clearedState⟩ ⟨(3, 0), joined, clearedState⟩ := by
  refine .next (by cbv) (.control (branch := .conditional 3 3 [] 4 []) (by cbv) ?_) (.done 0 (by cbv))
  cbv

theorem actual_taken_traversal : DemandTraversal context sampledAt 9 9
    ⟨(0, 2), sampled, initialState⟩ ⟨(3, 0), joined, clearedState⟩ := by
  exact shortCircuit_taken_traversal (isAnd := true) (condition := 2) (rhs := 1) (join := 2) (result := 3)
    (value := 5) (le := environment true true) (point := (0, 3)) (rightPoint := (1, 5))
    (frame := conditioned) (rightFrame := leftScope) (state := initialState) (rightState := clearedState)
    (selected := true) (leftLength := 1) (rightLength := 5) (continuationLength := 1) (fuel := 0)
    (forked := (demandShortCircuitFork true (.bool true) (environment true true) (indexBefore true true)).2)
    (before := (lowerExpr (.bool true) (environment true true) (indexBefore true true)).2)
    (ended := (lowerExpr right (environment true true)
      (demandShortCircuitRightBefore true (.bool true) (environment true true) (indexBefore true true))).2)
    rfl (by cbv) (forkExtended true true) (by cbv) (by cbv) (jumpExtended true true) (by cbv)
    leftTraversal rightTraversal continuationTraversal

theorem actual_taken_runtime_prefix_rows (world : World) (env : Env)
    {taken : Nat} {runtime : DemandRuntimePoint} (bound : taken ≤ 9)
    (steps : DemandRuntimePrefix context taken ⟨(0, 2), sampled, initialState⟩ runtime) :
    required.Realizes (sourceModule true true) world env runtime :=
  sampled_rows_realize world env (actual_taken_traversal.runtimePrefix_invariant bound steps)

theorem actual_taken_runtime_prefix_sample_read (world : World) (env : Env)
    {taken : Nat} {runtime : DemandRuntimePoint} (bound : taken ≤ 9)
    (steps : DemandRuntimePrefix context taken ⟨(0, 2), sampled, initialState⟩ runtime) :
    ∃ values, (getView runtime.frame 1 >>= readRun) runtime.state = .ok values runtime.state :=
  ((actual_taken_runtime_prefix_rows world env bound steps).2 (1, sampledAlias) (by simp [required])).read_safe

private def skipContext : FnCtx := ⟨⟨.release, lower (sourceModule true false)⟩, function true false⟩
private def falseConditioned : GIR.Frame := sampled.set 2 (.val (.bool false))
private def skipJoined : GIR.Frame := falseConditioned.set 3 (.val (.bool false))

private theorem skipLeftTraversal : DemandTraversal skipContext sampledAt 1 3
    ⟨(0, 2), sampled, initialState⟩ ⟨(0, 3), falseConditioned, initialState⟩ := by
  refine .next (by cbv) (.definition (id := 2) (op := .constBool false) (by cbv) (by rfl))
    (.done 2 (by cbv))

private theorem skipContinuationTraversal : DemandTraversal skipContext sampledAt 1 1
    ⟨(2, 0), skipJoined, initialState⟩ ⟨(4, 0), skipJoined, initialState⟩ := by
  refine .next (by cbv) (.control (branch := .conditional 3 3 [] 4 []) (by cbv) ?_) (.done 0 (by cbv))
  cbv

theorem actual_skip_traversal : DemandTraversal skipContext sampledAt 3 3
    ⟨(0, 2), sampled, initialState⟩ ⟨(4, 0), skipJoined, initialState⟩ := by
  exact shortCircuit_skip_traversal (isAnd := true) (condition := 2) (rhs := 1) (join := 2) (result := 3)
    (le := environment true false) (point := (0, 3)) (frame := falseConditioned) (state := initialState)
    (leftLength := 1) (continuationLength := 1) (fuel := 0)
    (forked := (demandShortCircuitFork true (.bool false) (environment true false) (indexBefore true false)).2)
    (before := (lowerExpr (.bool false) (environment true false) (indexBefore true false)).2)
    rfl (by cbv) (forkExtended true false) (by cbv) skipLeftTraversal skipContinuationTraversal

theorem actual_skip_runtime_prefix_rows (world : World) (env : Env)
    {taken : Nat} {runtime : DemandRuntimePoint} (bound : taken ≤ 3)
    (steps : DemandRuntimePrefix skipContext taken ⟨(0, 2), sampled, initialState⟩ runtime) :
    required.Realizes (sourceModule true true) world env runtime :=
  sampled_rows_realize world env (actual_skip_traversal.runtimePrefix_invariant bound steps)

theorem physically_removed_run_rejected (world : World) (env : Env) :
    ¬ required.Realizes (sourceModule true true) world env
      ⟨(1, 3), addressed, LifetimeChecks.removedSample⟩ := by
  intro realized
  obtain ⟨values, read⟩ := (realized.2 (1, sampledAlias) (by simp [required])).read_safe
  have faulted : (getView addressed 1 >>= readRun) LifetimeChecks.removedSample =
      .stop (.fault .pathRange) LifetimeChecks.removedSample := by cbv
  rw [faulted] at read
  cases read


end Goose.Lower.DemandGeneratedShortCircuitChecks

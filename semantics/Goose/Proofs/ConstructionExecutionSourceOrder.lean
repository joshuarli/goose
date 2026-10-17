import Goose.Construct.Eval
import Goose.Proofs.ExitExecution

namespace Goose.Proofs.ConstructionExecution
open Goose.Construct

inductive ListMapMLoopSuccess (action : α → EvalM β) :
    List α → List β → ExecutionState → List β → ExecutionState → Prop
  | nil (accumulator : List β) (state : ExecutionState) :
      ListMapMLoopSuccess action [] accumulator state accumulator.reverse state
  | cons {item : α} {rest : List α} {accumulator : List β}
      {initial middle final : ExecutionState} {value : β} {values : List β}
      (head : action item initial = .ok value middle)
      (tail : ListMapMLoopSuccess action rest (value :: accumulator) middle values final) :
      ListMapMLoopSuccess action (item :: rest) accumulator initial values final

inductive ListMapMLoopStopped (action : α → EvalM β) :
    List α → List β → ExecutionState → Goose.Core.Stop → ExecutionState → List α → Prop
  | atHead {item : α} {rest : List α} {accumulator : List β}
      {initial final : ExecutionState} {reason : Goose.Core.Stop}
      (head : action item initial = .stop reason final) :
      ListMapMLoopStopped action (item :: rest) accumulator initial reason final [item]
  | afterHead {item : α} {rest visited : List α} {accumulator : List β}
      {initial middle final : ExecutionState} {value : β} {reason : Goose.Core.Stop}
      (head : action item initial = .ok value middle)
      (tail : ListMapMLoopStopped action rest (value :: accumulator) middle reason final visited) :
      ListMapMLoopStopped action (item :: rest) accumulator initial reason final (item :: visited)

inductive ListMapMLoopEscaped (action : α → EvalM β) :
    List α → List β → ExecutionState → ExitAddress → List Carrier → ExecutionState → List α → Prop
  | atHead {item : α} {rest : List α} {accumulator : List β}
      {initial final : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
      (head : action item initial = .escape address carriers final) :
      ListMapMLoopEscaped action (item :: rest) accumulator initial address carriers final [item]
  | afterHead {item : α} {rest visited : List α} {accumulator : List β}
      {initial middle final : ExecutionState} {value : β} {address : ExitAddress}
      {carriers : List Carrier}
      (head : action item initial = .ok value middle)
      (tail : ListMapMLoopEscaped action rest (value :: accumulator) middle address carriers final visited) :
      ListMapMLoopEscaped action (item :: rest) accumulator initial address carriers final
        (item :: visited)

def SourcePrefix (visited inputs : List α) : Prop :=
  ∃ suffix, inputs = visited ++ suffix

theorem listMapMLoop_success_trace (action : α → EvalM β) (inputs : List α)
    (accumulator : List β) (initial : ExecutionState) (values : List β) (final : ExecutionState)
    (result : List.mapM.loop action inputs accumulator initial = .ok values final) :
    ListMapMLoopSuccess action inputs accumulator initial values final := by
  induction inputs generalizing accumulator initial values final with
  | nil =>
      rw [List.mapM.loop.eq_1] at result
      simp only [pure] at result
      cases result
      exact .nil accumulator initial
  | cons item rest ih =>
      rw [List.mapM.loop.eq_2] at result
      cases head : action item initial with
      | ok value middle =>
          simp only [bind, head] at result
          exact .cons head (ih (value :: accumulator) middle values final result)
      | stop reason middle => simp only [bind, head] at result; cases result
      | escape address carriers middle => simp only [bind, head] at result; cases result
      | jump target kind middle => simp only [bind, head] at result; cases result

theorem listMapM_success_trace (action : α → EvalM β) (inputs : List α)
    (initial : ExecutionState) (values : List β) (final : ExecutionState)
    (result : (inputs.mapM action) initial = .ok values final) :
    ListMapMLoopSuccess action inputs [] initial values final := by
  apply listMapMLoop_success_trace action inputs [] initial values final
  simpa only [List.mapM] using result

theorem listMapMLoop_success_length (action : α → EvalM β) {inputs : List α}
    {accumulator : List β} {initial : ExecutionState} {values : List β} {final : ExecutionState}
    (trace : ListMapMLoopSuccess action inputs accumulator initial values final) :
    values.length = inputs.length + accumulator.length := by
  induction trace with
  | nil accumulator state => simp
  | @cons item rest accumulator initial middle final value values head tail ih =>
      simp only [List.length_cons] at ih ⊢
      omega

theorem listMapMLoop_stopped_trace (action : α → EvalM β) (inputs : List α)
    (accumulator : List β) (initial : ExecutionState) (reason : Goose.Core.Stop)
    (final : ExecutionState)
    (result : List.mapM.loop action inputs accumulator initial = .stop reason final) :
    ∃ visited, ListMapMLoopStopped action inputs accumulator initial reason final visited := by
  induction inputs generalizing accumulator initial reason final with
  | nil =>
      rw [List.mapM.loop.eq_1] at result
      simp only [pure] at result
      cases result
  | cons item rest ih =>
      rw [List.mapM.loop.eq_2] at result
      cases head : action item initial with
      | ok value middle =>
          simp only [bind, head] at result
          obtain ⟨visited, tail⟩ := ih (value :: accumulator) middle reason final result
          exact ⟨item :: visited, .afterHead head tail⟩
      | stop stopped final' =>
          simp only [bind, head] at result
          cases result
          exact ⟨[item], .atHead (rest := rest) (accumulator := accumulator) head⟩
      | escape address carriers final' => simp only [bind, head] at result; cases result
      | jump target kind final' => simp only [bind, head] at result; cases result

theorem sourcePrefix_of_stopped {action : α → EvalM β} {inputs : List α}
    {accumulator : List β} {initial : ExecutionState} {reason : Goose.Core.Stop}
    {final : ExecutionState} {visited : List α}
    (trace : ListMapMLoopStopped action inputs accumulator initial reason final visited) :
    SourcePrefix visited inputs := by
  induction trace with
  | atHead head => exact ⟨_, rfl⟩
  | @afterHead item rest visited accumulator initial middle final value reason head tail ih =>
      obtain ⟨suffix, suffixEq⟩ := ih
      exact ⟨suffix, by simp [suffixEq]⟩

theorem listMapM_stopped_source_prefix (action : α → EvalM β) (inputs : List α)
    (initial final : ExecutionState) (reason : Goose.Core.Stop)
    (result : (inputs.mapM action) initial = .stop reason final) :
    ∃ visited, SourcePrefix visited inputs := by
  change List.mapM.loop action inputs [] initial = .stop reason final at result
  obtain ⟨visited, trace⟩ := listMapMLoop_stopped_trace action inputs [] initial reason final result
  exact ⟨visited, sourcePrefix_of_stopped trace⟩

theorem listMapMLoop_escaped_trace (action : α → EvalM β) (inputs : List α)
    (accumulator : List β) (initial : ExecutionState) (address : ExitAddress)
    (carriers : List Carrier) (final : ExecutionState)
    (result : List.mapM.loop action inputs accumulator initial =
      .escape address carriers final) :
    ∃ visited, ListMapMLoopEscaped action inputs accumulator initial address carriers final visited := by
  induction inputs generalizing accumulator initial address carriers final with
  | nil =>
      rw [List.mapM.loop.eq_1] at result
      simp only [pure] at result
      cases result
  | cons item rest ih =>
      rw [List.mapM.loop.eq_2] at result
      cases head : action item initial with
      | ok value middle =>
          simp only [bind, head] at result
          obtain ⟨visited, tail⟩ := ih (value :: accumulator) middle address carriers final result
          exact ⟨item :: visited, .afterHead head tail⟩
      | stop reason final' => simp only [bind, head] at result; cases result
      | escape escapedAddress escapedCarriers final' =>
          simp only [bind, head] at result
          cases result
          exact ⟨[item], .atHead (rest := rest) (accumulator := accumulator) head⟩
      | jump target kind final' => simp only [bind, head] at result; cases result

theorem sourcePrefix_of_escaped {action : α → EvalM β} {inputs : List α}
    {accumulator : List β} {initial : ExecutionState} {address : ExitAddress}
    {carriers : List Carrier} {final : ExecutionState} {visited : List α}
    (trace : ListMapMLoopEscaped action inputs accumulator initial address carriers final visited) :
    SourcePrefix visited inputs := by
  induction trace with
  | atHead head => exact ⟨_, rfl⟩
  | @afterHead item rest visited accumulator initial middle final value address carriers head tail ih =>
      obtain ⟨suffix, suffixEq⟩ := ih
      exact ⟨suffix, by simp [suffixEq]⟩

theorem listMapM_escaped_source_prefix (action : α → EvalM β) (inputs : List α)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (result : (inputs.mapM action) initial = .escape address carriers final) :
    ∃ visited, SourcePrefix visited inputs := by
  change List.mapM.loop action inputs [] initial = .escape address carriers final at result
  obtain ⟨visited, trace⟩ :=
    listMapMLoop_escaped_trace action inputs [] initial address carriers final result
  exact ⟨visited, sourcePrefix_of_escaped trace⟩

theorem listMapM_success_length (action : α → EvalM β) (inputs : List α)
    (initial : ExecutionState) (values : List β) (final : ExecutionState)
    (result : (inputs.mapM action) initial = .ok values final) :
    values.length = inputs.length := by
  have trace := listMapM_success_trace action inputs initial values final result
  simpa using listMapMLoop_success_length action trace

inductive EvalOperandsSuccess (config : EvalConfig) (environment : RuntimeActivation) :
    Nat → List Channel → List Expr → ExecutionState → List Carrier → ExecutionState → Prop
  | nil (fuel : Nat) (state : ExecutionState) :
      EvalOperandsSuccess config environment fuel [] [] state [] state
  | cons {fuel : Nat} {channel : Channel} {channels : List Channel} {operand : Expr}
      {operands : List Expr}
      {initial producedState middle final : ExecutionState} {produced : List Carrier}
      {carrier : Carrier} {carriers : List Carrier}
      (produce : evalProduce fuel config environment [channel] operand initial =
        .ok produced producedState)
      (single : singleCarrier produced producedState = .ok carrier middle)
      (tail : EvalOperandsSuccess config environment fuel channels operands middle carriers final) :
      EvalOperandsSuccess config environment (fuel + 1) (channel :: channels)
        (operand :: operands) initial (carrier :: carriers) final

theorem evalOperands_success_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) :
    ∀ {channels : List Channel} {operands : List Expr} {initial final : ExecutionState}
      {carriers : List Carrier},
      evalOperands fuel config environment channels operands initial = .ok carriers final →
      EvalOperandsSuccess config environment fuel channels operands initial carriers final := by
  induction fuel with
  | zero =>
      intro channels operands initial final carriers result
      simp only [evalOperands, timeout, EvalM.stop] at result
      cases result
  | succ fuel ih =>
      intro channels operands initial final carriers result
      cases channels with
      | nil =>
          cases operands with
          | nil =>
              simp only [evalOperands, pure] at result
              cases result
              exact .nil _ initial
          | cons operand operands =>
              simp only [evalOperands, fault, EvalM.stop] at result
              cases result
      | cons channel channels =>
          cases operands with
          | nil =>
              simp only [evalOperands, fault, EvalM.stop] at result
              cases result
          | cons operand operands =>
              simp only [evalOperands] at result
              cases produce : evalProduce fuel config environment [channel] operand initial with
              | ok produced producedState =>
                  simp only [bind, produce] at result
                  cases single : singleCarrier produced producedState with
                  | ok carrier middle =>
                      simp only [single] at result
                      cases tail : evalOperands fuel config environment channels operands middle with
                      | ok remaining final' =>
                          simp only [tail, pure] at result
                          injection result with carriersEq stateEq
                          subst carriers
                          subst final
                          exact .cons produce single (ih tail)
                      | stop reason final' => simp only [tail] at result; cases result
                      | escape address exits final' => simp only [tail] at result; cases result
                      | jump target kind final' => simp only [tail] at result; cases result
                  | stop reason middle => simp only [single] at result; cases result
                  | escape address exits middle => simp only [single] at result; cases result
                  | jump target kind middle => simp only [single] at result; cases result
              | stop reason middle => simp only [bind, produce] at result; cases result
              | escape address exits middle => simp only [bind, produce] at result; cases result
              | jump target kind middle => simp only [bind, produce] at result; cases result

theorem evalOperands_success_count (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) {channels : List Channel} {operands : List Expr}
    {initial final : ExecutionState} {carriers : List Carrier}
    (trace : EvalOperandsSuccess config environment fuel channels operands initial carriers final) :
    carriers.length = operands.length := by
  induction trace with
  | nil _ state => rfl
  | @cons fuel channel channels operand operands initial middle final carrier carriers head tail ih =>
      simp only [List.length_cons] at ih ⊢
      omega

theorem evalProduce_values_success_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (operands : List Expr)
    (initial final : ExecutionState) (carriers : List Carrier)
    (result : evalProduce (fuel + 1) config environment channels (.values operands) initial =
      .ok carriers final) :
    EvalOperandsSuccess config environment fuel channels operands initial carriers final := by
  apply evalOperands_success_trace fuel config environment
  simpa only [evalProduce] using result

theorem evalProduce_values_success_count (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (operands : List Expr)
    (initial final : ExecutionState) (carriers : List Carrier)
    (result : evalProduce (fuel + 1) config environment channels (.values operands) initial =
      .ok carriers final) :
    carriers.length = operands.length :=
  evalOperands_success_count fuel config environment (evalProduce_values_success_trace
    fuel config environment channels operands initial final carriers result)

theorem evalValue_fixedFill_source_once (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (element : Ty) (count : Nat) (operand : Expr)
    (origin : Goose.Core.OriginId) (initial final : ExecutionState) (values : Array Value)
    (fixed : (Ty.arr element count).nonfixed = false)
    (result : evalValue (fuel + 1) config environment (.fill (.arr element count) operand origin)
      initial = .ok (.fixed values) final) :
    ∃ value, evalValue fuel config environment operand initial = .ok value final ∧
      values = Array.replicate count value := by
  simp only [evalValue] at result
  have notTrue : ¬ (Ty.arr element count).nonfixed = true := by simp [fixed]
  rw [ite_eq_right notTrue] at result
  simp only [bind, pure] at result
  cases operandResult : evalValue fuel config environment operand initial with
  | ok value final' =>
      rw [operandResult] at result
      have valuesEq : values = Array.replicate count value := by
        injection result with valueEq stateEq
        injection valueEq with valuesEq
        exact valuesEq.symm
      have finalEq : final' = final := by injection result
      subst final'
      exact ⟨value, rfl, valuesEq⟩
  | stop reason final' => rw [operandResult] at result; cases result
  | escape address carriers final' => rw [operandResult] at result; cases result
  | jump target kind final' => rw [operandResult] at result; cases result

theorem evalValue_fixedArray_operands_success_order (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (initial final : ExecutionState) (values : List Value)
    (fixed : ty.nonfixed = false)
    (result : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial =
      .ok (.fixed values.toArray) final) :
    ListMapMLoopSuccess (fun operand => evalValue fuel config environment operand)
      operands [] initial values final := by
  simp only [evalValue] at result
  have notTrue : ¬ ty.nonfixed = true := by simp [fixed]
  rw [ite_eq_right notTrue] at result
  simp only [bind, pure] at result
  cases operandsResult : operands.mapM (evalValue fuel config environment) initial with
  | ok evaluated final' =>
      simp only [operandsResult] at result
      have arrayEq : evaluated.toArray = values.toArray := by
        have valueEq : Value.fixed evaluated.toArray = Value.fixed values.toArray := by
          injection result with valueEq stateEq
        injection valueEq with arrayEq
      have listEq : evaluated = values := by
        have listArrayEq := congrArg Array.toList arrayEq
        simpa using listArrayEq
      have stateEq : final' = final := by injection result
      subst final'
      rw [← listEq]
      exact listMapM_success_trace _ _ _ _ _ operandsResult
  | stop reason final' => simp only [operandsResult] at result; cases result
  | escape address carriers final' => simp only [operandsResult] at result; cases result
  | jump target kind final' => simp only [operandsResult] at result; cases result

theorem evalValue_fixedArray_operands_stopped_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (reason : Goose.Core.Stop) (initial final : ExecutionState)
    (fixed : ty.nonfixed = false)
    (result : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial =
      .stop reason final) :
    ∃ visited, ListMapMLoopStopped (fun operand => evalValue fuel config environment operand)
      operands [] initial reason final visited := by
  simp only [evalValue] at result
  have notTrue : ¬ ty.nonfixed = true := by simp [fixed]
  rw [ite_eq_right notTrue] at result
  simp only [bind, pure] at result
  cases operandsResult : operands.mapM (evalValue fuel config environment) initial with
  | ok evaluated final' => simp only [operandsResult] at result; cases result
  | stop stopped final' =>
      simp only [operandsResult] at result
      cases result
      exact listMapMLoop_stopped_trace _ _ [] _ reason _ operandsResult
  | escape address carriers final' => simp only [operandsResult] at result; cases result
  | jump target kind final' => simp only [operandsResult] at result; cases result

theorem evalValue_fixedArray_operands_stopped_prefix (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (reason : Goose.Core.Stop) (initial final : ExecutionState)
    (fixed : ty.nonfixed = false)
    (result : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial =
      .stop reason final) :
    ∃ visited, SourcePrefix visited operands := by
  obtain ⟨visited, trace⟩ := evalValue_fixedArray_operands_stopped_trace
    fuel config environment ty operands origin reason initial final fixed result
  exact ⟨visited, sourcePrefix_of_stopped trace⟩

theorem evalValue_fixedArray_operands_escaped_trace (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (address : ExitAddress) (carriers : List Carrier)
    (initial final : ExecutionState) (fixed : ty.nonfixed = false)
    (result : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial =
      .escape address carriers final) :
    ∃ visited, ListMapMLoopEscaped (fun operand => evalValue fuel config environment operand)
      operands [] initial address carriers final visited := by
  simp only [evalValue] at result
  have notTrue : ¬ ty.nonfixed = true := by simp [fixed]
  rw [ite_eq_right notTrue] at result
  simp only [bind, pure] at result
  cases operandsResult : operands.mapM (evalValue fuel config environment) initial with
  | ok evaluated final' => simp only [operandsResult] at result; cases result
  | stop reason final' => simp only [operandsResult] at result; cases result
  | escape address' carriers' final' =>
      simp only [operandsResult] at result
      cases result
      exact listMapMLoop_escaped_trace _ _ [] _ address carriers _ operandsResult
  | jump target kind final' => simp only [operandsResult] at result; cases result

theorem evalValue_fixedArray_operands_escaped_prefix (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (address : ExitAddress) (carriers : List Carrier)
    (initial final : ExecutionState) (fixed : ty.nonfixed = false)
    (result : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial =
      .escape address carriers final) :
    ∃ visited, SourcePrefix visited operands := by
  obtain ⟨visited, trace⟩ := evalValue_fixedArray_operands_escaped_trace
    fuel config environment ty operands origin address carriers initial final fixed result
  exact ⟨visited, sourcePrefix_of_escaped trace⟩

end Goose.Proofs.ConstructionExecution

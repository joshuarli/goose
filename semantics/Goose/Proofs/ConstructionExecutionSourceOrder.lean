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

end Goose.Proofs.ConstructionExecution

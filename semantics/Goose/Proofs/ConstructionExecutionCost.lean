import Goose.Proofs.ConstructionExecutionSourceOrder

namespace Goose.Proofs.ConstructionExecution
open Goose.Construct

inductive ListMapMOperandCost (action : α → EvalM β) (inputs : List α)
    (initial : ExecutionState) : ExecutionStep (List β) → Prop
  | completed {values : List β} {final : ExecutionState}
      (trace : ListMapMLoopSuccess action inputs [] initial values final) :
      ListMapMOperandCost action inputs initial (.ok values final)
  | stopped {reason : Goose.Core.Stop} {final : ExecutionState} {visited : List α}
      (trace : ListMapMLoopStopped action inputs [] initial reason final visited) :
      ListMapMOperandCost action inputs initial (.stop reason final)
  | escaped {address : ExitAddress} {carriers : List Carrier} {final : ExecutionState}
      {visited : List α}
      (trace : ListMapMLoopEscaped action inputs [] initial address carriers final visited) :
      ListMapMOperandCost action inputs initial (.escape address carriers final)
  | jumped {target : Nat} {kind : JumpKind} {final : ExecutionState} {visited : List α}
      (trace : ListMapMLoopJumped action inputs [] initial target kind final visited) :
      ListMapMOperandCost action inputs initial (.jump target kind final)

theorem listMapM_operand_cost (action : α → EvalM β) (inputs : List α)
    (initial : ExecutionState) :
    ListMapMOperandCost action inputs initial ((inputs.mapM action) initial) := by
  cases result : (inputs.mapM action) initial with
  | ok values final =>
      exact .completed (listMapM_success_trace action inputs initial values final result)
  | stop reason final =>
      obtain ⟨visited, trace⟩ := listMapMLoop_stopped_trace action inputs [] initial reason final
        (by simpa only [List.mapM] using result)
      exact .stopped trace
  | escape address carriers final =>
      obtain ⟨visited, trace⟩ := listMapMLoop_escaped_trace action inputs [] initial address carriers
        final (by simpa only [List.mapM] using result)
      exact .escaped trace
  | jump target kind final =>
      obtain ⟨visited, trace⟩ := listMapMLoop_jumped_trace action inputs [] initial target kind final
        (by simpa only [List.mapM] using result)
      exact .jumped trace

theorem listMapM_operand_cost_prefix {action : α → EvalM β} {inputs : List α}
    {initial : ExecutionState} {result : ExecutionStep (List β)}
    (cost : ListMapMOperandCost action inputs initial result) :
    ∃ visited, SourcePrefix visited inputs ∧ visited.length ≤ inputs.length := by
  cases cost with
  | completed trace => exact ⟨inputs, ⟨[], by simp⟩, Nat.le_refl _⟩
  | stopped trace =>
      exact ⟨_, sourcePrefix_of_stopped trace, sourcePrefix_length_le (sourcePrefix_of_stopped trace)⟩
  | escaped trace =>
      exact ⟨_, sourcePrefix_of_escaped trace, sourcePrefix_length_le (sourcePrefix_of_escaped trace)⟩
  | jumped trace =>
      exact ⟨_, sourcePrefix_of_jumped trace, sourcePrefix_length_le (sourcePrefix_of_jumped trace)⟩

def fixedArrayOperandResult : ExecutionStep (List Value) → ExecutionStep Value
  | .ok values final => .ok (.fixed values.toArray) final
  | .stop reason final => .stop reason final
  | .escape address carriers final => .escape address carriers final
  | .jump target kind final => .jump target kind final

structure FixedArrayOperandCost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (initial : ExecutionState) (outcome : ExecutionStep Value) where
  mapped : ExecutionStep (List Value)
  mapResult : (operands.mapM (evalValue fuel config environment)) initial = mapped
  loop : ListMapMOperandCost (evalValue fuel config environment) operands initial mapped
  output : outcome = fixedArrayOperandResult mapped

def evalValue_fixedArray_operand_cost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (initial : ExecutionState) (outcome : ExecutionStep Value)
    (fixed : ty.nonfixed = false)
    (result : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial = outcome) :
    FixedArrayOperandCost fuel config environment ty operands origin initial outcome := by
  simp only [evalValue] at result
  have notTrue : ¬ ty.nonfixed = true := by simp [fixed]
  rw [ite_eq_right notTrue] at result
  simp only [bind, pure] at result
  cases mapResult : (operands.mapM (evalValue fuel config environment)) initial with
  | ok values final =>
      simp only [mapResult] at result
      have output : outcome = fixedArrayOperandResult (.ok values final) := by
        cases result
        rfl
      exact ⟨.ok values final, mapResult,
        .completed (listMapM_success_trace _ _ _ _ _ mapResult), output⟩
  | stop reason final =>
      simp only [mapResult] at result
      have output : outcome = fixedArrayOperandResult (.stop reason final) := by
        cases result
        rfl
      exact ⟨.stop reason final, mapResult, by
        obtain ⟨visited, trace⟩ := listMapMLoop_stopped_trace (evalValue fuel config environment)
          operands [] initial reason final (by simpa only [List.mapM] using mapResult)
        exact .stopped trace, output⟩
  | escape address carriers final =>
      simp only [mapResult] at result
      have output : outcome = fixedArrayOperandResult (.escape address carriers final) := by
        cases result
        rfl
      exact ⟨.escape address carriers final, mapResult, by
        obtain ⟨visited, trace⟩ := listMapMLoop_escaped_trace (evalValue fuel config environment)
          operands [] initial address carriers final (by simpa only [List.mapM] using mapResult)
        exact .escaped trace, output⟩
  | jump target kind final =>
      simp only [mapResult] at result
      have output : outcome = fixedArrayOperandResult (.jump target kind final) := by
        cases result
        rfl
      exact ⟨.jump target kind final, mapResult, by
        obtain ⟨visited, trace⟩ := listMapMLoop_jumped_trace (evalValue fuel config environment)
          operands [] initial target kind final (by simpa only [List.mapM] using mapResult)
        exact .jumped trace, output⟩

theorem evalValue_fixedArray_operand_cost_prefix {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {ty : Ty} {operands : List Expr}
    {origin : Goose.Core.OriginId} {initial : ExecutionState} {outcome : ExecutionStep Value}
    (cost : FixedArrayOperandCost fuel config environment ty operands origin initial outcome) :
    ∃ visited, SourcePrefix visited operands ∧ visited.length ≤ operands.length :=
  listMapM_operand_cost_prefix cost.loop

def recordOperandResult (id : Goose.Core.StructId) :
    ExecutionStep (List Value) → ExecutionStep Value
  | .ok values final => .ok (.record id values.toArray) final
  | .stop reason final => .stop reason final
  | .escape address carriers final => .escape address carriers final
  | .jump target kind final => .jump target kind final

structure RecordOperandCost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id : Goose.Core.StructId) (fields : TyList)
    (operands : List Expr) (initial : ExecutionState) (outcome : ExecutionStep Value) where
  mapped : ExecutionStep (List Value)
  mapResult : (operands.mapM (evalValue fuel config environment)) initial = mapped
  loop : ListMapMOperandCost (evalValue fuel config environment) operands initial mapped
  output : outcome = recordOperandResult id mapped

def evalValue_structLiteral_operand_cost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id : Goose.Core.StructId) (fields : TyList)
    (operands : List Expr) (initial : ExecutionState) (outcome : ExecutionStep Value)
    (result : evalValue (fuel + 1) config environment (.structLit (.structT id fields) operands)
      initial = outcome) :
    RecordOperandCost fuel config environment id fields operands initial outcome := by
  simp only [evalValue, bind, pure] at result
  cases mapResult : (operands.mapM (evalValue fuel config environment)) initial with
  | ok values final =>
      simp only [mapResult] at result
      have output : outcome = recordOperandResult id (.ok values final) := by
        cases result
        rfl
      exact ⟨.ok values final, mapResult,
        .completed (listMapM_success_trace _ _ _ _ _ mapResult), output⟩
  | stop reason final =>
      simp only [mapResult] at result
      have output : outcome = recordOperandResult id (.stop reason final) := by
        cases result
        rfl
      exact ⟨.stop reason final, mapResult, by
        obtain ⟨visited, trace⟩ := listMapMLoop_stopped_trace (evalValue fuel config environment)
          operands [] initial reason final (by simpa only [List.mapM] using mapResult)
        exact .stopped trace, output⟩
  | escape address carriers final =>
      simp only [mapResult] at result
      have output : outcome = recordOperandResult id (.escape address carriers final) := by
        cases result
        rfl
      exact ⟨.escape address carriers final, mapResult, by
        obtain ⟨visited, trace⟩ := listMapMLoop_escaped_trace (evalValue fuel config environment)
          operands [] initial address carriers final (by simpa only [List.mapM] using mapResult)
        exact .escaped trace, output⟩
  | jump target kind final =>
      simp only [mapResult] at result
      have output : outcome = recordOperandResult id (.jump target kind final) := by
        cases result
        rfl
      exact ⟨.jump target kind final, mapResult, by
        obtain ⟨visited, trace⟩ := listMapMLoop_jumped_trace (evalValue fuel config environment)
          operands [] initial target kind final (by simpa only [List.mapM] using mapResult)
        exact .jumped trace, output⟩

theorem evalValue_structLiteral_operand_cost_prefix {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {id : Goose.Core.StructId} {fields : TyList}
    {operands : List Expr} {initial : ExecutionState} {outcome : ExecutionStep Value}
    (cost : RecordOperandCost fuel config environment id fields operands initial outcome) :
    ∃ visited, SourcePrefix visited operands ∧ visited.length ≤ operands.length :=
  listMapM_operand_cost_prefix cost.loop

structure NonfixedArrayOperandCost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (initial : ExecutionState) (outcome : ExecutionStep Value) where
  evaluation : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial = outcome
  traversal : NonfixedArrayEvalTraversal fuel config environment ty operands origin initial

theorem evalValue_nonfixedArray_operand_cost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (initial : ExecutionState) (outcome : ExecutionStep Value)
    (nonfixed : ty.nonfixed = true)
    (result : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial = outcome) :
    NonfixedArrayOperandCost fuel config environment ty operands origin initial outcome := by
  exact ⟨result, evalValue_nonfixedArray_operand_traversal fuel config environment ty operands origin
    initial outcome nonfixed result⟩

theorem evalValue_nonfixedArray_operand_cost_prefix {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {ty : Ty} {operands : List Expr}
    {origin : Goose.Core.OriginId} {initial : ExecutionState} {outcome : ExecutionStep Value}
    (cost : NonfixedArrayOperandCost fuel config environment ty operands origin initial outcome) :
    ∃ visited, SourcePrefix visited operands ∧ visited.length ≤ operands.length :=
  nonfixedArrayEvalTraversal_prefix cost.traversal

end Goose.Proofs.ConstructionExecution

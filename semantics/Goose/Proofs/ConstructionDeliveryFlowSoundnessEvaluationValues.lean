import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationValuesAccess
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationValuesConstruct

set_option Elab.async false
set_option maxHeartbeats 1600000

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

private theorem value_lit_succ (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation)
    (integer : Goose.Core.IntTy) (value : Int) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.lit integer value) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.lit integer value)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.lit integer value)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    simp only [evalValue]
    evaluation_values_normal

private theorem value_bool_succ (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation)
    (value : Bool) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.bool value) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.bool value)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.bool value)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    simp only [evalValue]
    evaluation_values_normal

private theorem value_read_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (place : Place) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.read place) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.read place)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.read place)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : placeQueryBudget place + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (placeFlows staticFuel place) (fun _ => normalFlow) _
    simp only [evalValue]
    apply controlFlow_suffix
    · exact previous.place environment place staticFuel (by omega)
    · intro result; evaluation_values_normal

private theorem value_ref_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (mutability : Goose.Core.Mutability) (place : Place) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.ref mutability place) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.ref mutability place)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.ref mutability place)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : placeQueryBudget place + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (placeFlows staticFuel place) (fun _ => normalFlow) _
    simp only [evalValue]
    apply controlFlow_suffix
    · exact previous.place environment place staticFuel (by omega)
    · intro result; evaluation_values_normal

private theorem value_len_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (view : View) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.len view) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.len view)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.len view)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : viewQueryBudget view + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (viewFlows staticFuel view) (fun _ => normalFlow) _
    simp only [evalValue]
    apply controlFlow_suffix
    · exact previous.view environment view staticFuel (by omega)
    · intro result; evaluation_values_normal

private theorem value_un_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.UnOp) (operand : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.un operation operand origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.un operation operand origin)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.un operation operand origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget operand + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (expressionFlows staticFuel operand) (fun _ => normalFlow) _
    simp only [evalValue]
    apply controlFlow_suffix
    · exact previous.value environment operand staticFuel (by omega)
    · intro result; evaluation_values_normal

private theorem value_not_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (operand : Expr) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.not operand) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.not operand)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.not operand)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget operand + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (expressionFlows staticFuel operand) (fun _ => normalFlow) _
    simp only [evalValue]
    apply controlFlow_suffix
    · exact previous.value environment operand staticFuel (by omega)
    · intro result; evaluation_values_normal

private theorem value_conv_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (kind : Goose.Core.ConvKind) (target : Ty) (operand : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.conv kind target operand origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.conv kind target operand origin)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.conv kind target operand origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget operand + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (expressionFlows staticFuel operand) (fun _ => normalFlow) _
    simp only [evalValue]
    apply controlFlow_suffix
    · exact previous.value environment operand staticFuel (by omega)
    · intro result; evaluation_values_normal

private theorem value_pop_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (owner : Place) (origin : Goose.Core.OriginId) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.pop owner origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.pop owner origin)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.pop owner origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : placeQueryBudget owner + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (placeFlows staticFuel owner) (fun _ => normalFlow) _
    simp only [evalValue]
    apply controlFlow_suffix
    · exact previous.place environment owner staticFuel (by omega)
    · intro result; evaluation_values_normal

private theorem value_bin_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.BinOp) (left right : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.bin operation left right origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.bin operation left right origin)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.bin operation left right origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget left + expressionQueryBudget right + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act
      (continueFlows (expressionFlows staticFuel left) (expressionFlows staticFuel right)) (fun _ => normalFlow) _
    simp only [evalValue]
    apply controlFlow_bind
    · exact previous.value environment left staticFuel (by omega)
    · intro leftValue
      apply controlFlow_prefix
      · evaluation_values_normal
      · rintro ⟨integer, first⟩
        apply controlFlow_suffix
        · exact previous.value environment right staticFuel (by omega)
        · intro rightValue; evaluation_values_normal

private theorem value_cmp_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.CmpOp) (left right : Expr) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.cmp operation left right) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.cmp operation left right)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.cmp operation left right)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget left + expressionQueryBudget right + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act
      (continueFlows (expressionFlows staticFuel left) (expressionFlows staticFuel right)) (fun _ => normalFlow) _
    simp only [evalValue]
    apply controlFlow_bind
    · exact previous.value environment left staticFuel (by omega)
    · intro leftValue
      apply controlFlow_suffix
      · exact previous.value environment right staticFuel (by omega)
      · intro rightValue; evaluation_values_normal

private theorem value_slice_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (mutability : Goose.Core.Mutability) (view : View) (lo hi : Bound) (origin : Goose.Core.OriginId) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.slice mutability view lo hi origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.slice mutability view lo hi origin)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.slice mutability view lo hi origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : viewQueryBudget view + boundQueryBudget lo + boundQueryBudget hi + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act
      (continueFlows (viewFlows staticFuel view) (continueFlows (boundFlows staticFuel lo) (boundFlows staticFuel hi))) (fun _ => normalFlow) _
    simp only [evalValue]
    apply controlFlow_bind
    · exact previous.view environment view staticFuel (by omega)
    · intro runtimeView
      apply controlFlow_bind
      · exact previous.bound environment runtimeView.count 0 lo staticFuel (by omega)
      · intro lower
        apply controlFlow_suffix
        · exact previous.bound environment runtimeView.count runtimeView.count hi staticFuel (by omega)
        · intro upper; evaluation_values_normal

private theorem value_call_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.call context arguments origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.call context arguments origin)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.call context arguments origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : argumentsQueryBudget arguments + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (argumentsFlows staticFuel arguments) (fun _ => normalFlow) _
    simp only [evalValue]
    apply controlFlow_prefix
    · evaluation_values_normal
    · rintro ⟨implementationId, implementation⟩
      apply controlFlow_prefix
      · evaluation_values_normal
      · intro channels
        apply controlFlow_suffix
        · exact previous.call environment context arguments channels origin staticFuel (by omega)
        · intro carriers; evaluation_values_normal

private theorem value_push_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (owner : Place) (operand : Expr) (origin : Option Goose.Core.OriginId) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.push owner operand origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.push owner operand origin)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.push owner operand origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    simp only [evalValue]
    exact previous.push environment owner operand origin (staticFuel + 1) enough

private theorem value_resultLocal_succ (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation)
    (variableId : Goose.Core.VarId) (origin : Goose.Core.OriginId) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.resultLocal variableId origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.resultLocal variableId origin)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.resultLocal variableId origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    simp only [evalValue]
    evaluation_values_normal

private theorem value_ifE_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (condition : Expr) (yes no : Block) (origin : Goose.Core.OriginId) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.ifE condition yes no origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.ifE condition yes no origin)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.ifE condition yes no origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget condition + blockQueryBudget yes + blockQueryBudget no + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act
      (continueFlows (expressionFlows staticFuel condition) (blockFlows staticFuel yes ++ blockFlows staticFuel no)) (fun _ => normalFlow) _
    simp only [evalValue]
    apply controlFlow_bind
    · exact previous.value environment condition staticFuel (by omega)
    · intro conditionValue
      apply controlFlow_prefix
      · evaluation_values_normal
      · intro boolean
        cases boolean with
        | true =>
          apply controlFlow_dispatch (blockFlows staticFuel yes) _ resultControlFlow (fun _ => normalFlow)
          · exact previous.block environment [] [] yes staticFuel (by omega)
          · intro scope kind present; exact List.mem_append_left _ present
          · intro flow present
            cases flow with
            | normal value => exact controlFlow_pure _ _ value (List.mem_append_left _ present)
            | breaking value => exact controlFlow_stop _ _ _
            | continuing => exact controlFlow_stop _ _ _
        | false =>
          apply controlFlow_dispatch (blockFlows staticFuel no) _ resultControlFlow (fun _ => normalFlow)
          · exact previous.block environment [] [] no staticFuel (by omega)
          · intro scope kind present; exact List.mem_append_right _ present
          · intro flow present
            cases flow with
            | normal value => exact controlFlow_pure _ _ value (List.mem_append_right _ present)
            | breaking value => exact controlFlow_stop _ _ _
            | continuing => exact controlFlow_stop _ _ _

private theorem value_blockE_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (body : Block) (origin : Goose.Core.OriginId) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.blockE body origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.blockE body origin)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.blockE body origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    simp only [evalValue]
    split
    · apply controlFlow_prefix
      · evaluation_values_normal
      · intro channels
        apply controlFlow_suffix
        · exact previous.produce environment channels (.blockE body origin) (staticFuel + 1) enough
        · intro carriers; evaluation_values_normal
    · exact controlFlow_stop _ _ _

private theorem value_arrLit_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (ty : Ty) (operands : List Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.arrLit ty operands origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.arrLit ty operands origin)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.arrLit ty operands origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionListQueryBudget operands + 1 ≤ staticFuel + 1 := enough
    simp only [evalValue]
    split
    · apply controlFlow_suffix
      · apply controlFlow_constructLocal
        intro destination
        exact previous.build environment destination (.arrLit ty operands origin) (staticFuel + 1) enough
      · intro carrier; evaluation_values_normal
    · change ControlFlowAction environment.act (expressionsFlows staticFuel operands) (fun _ => normalFlow) _
      apply controlFlow_map
      exact evaluationControl_values_map fuel config previous environment operands staticFuel (by omega)

private theorem value_fill_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (ty : Ty) (operand : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.fill ty operand origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.fill ty operand origin)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.fill ty operand origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget operand + 1 ≤ staticFuel + 1 := enough
    cases ty <;> simp only [evalValue]
    all_goals first | exact controlFlow_stop _ _ _ | skip
    case arr element count =>
      split
      · apply controlFlow_suffix
        · apply controlFlow_constructLocal
          intro destination
          exact previous.build environment destination (.fill (.arr element count) operand origin) (staticFuel + 1) enough
        · intro carrier; evaluation_values_normal
      · change ControlFlowAction environment.act (expressionFlows staticFuel operand) (fun _ => normalFlow) _
        apply controlFlow_suffix
        · exact previous.value environment operand staticFuel (by omega)
        · intro value; evaluation_values_normal

private theorem value_structLit_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (ty : Ty) (operands : List Expr) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.structLit ty operands) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.structLit ty operands)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.structLit ty operands)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionListQueryBudget operands + 1 ≤ staticFuel + 1 := enough
    cases ty <;> simp only [evalValue]
    all_goals first | exact controlFlow_stop _ _ _ | skip
    case structT id parameters =>
      change ControlFlowAction environment.act (expressionsFlows staticFuel operands) (fun _ => normalFlow) _
      apply controlFlow_map
      exact evaluationControl_values_map fuel config previous environment operands staticFuel (by omega)

private theorem value_bytes_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.bytes ty bytes origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.bytes ty bytes origin)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.bytes ty bytes origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have constructing : ControlFlowAction environment.act [normalFlow] (fun _ => normalFlow)
        (do carrierValue (← constructLocal ⟨config.module, environment.vars⟩ environment.act ty origin
          (.bytes ty bytes origin) (fun destination => buildExpr fuel config environment destination (.bytes ty bytes origin)))) := by
      apply controlFlow_suffix
      · apply controlFlow_constructLocal
        intro destination
        exact previous.build environment destination (.bytes ty bytes origin) (staticFuel + 1) enough
      · intro carrier; evaluation_values_normal
    cases ty with
    | int integer =>
      simp only [evalValue]
      repeat' first | exact constructing | (solve | evaluation_values_normal) | split
    | bool =>
      simp only [evalValue]
      repeat' first | exact constructing | (solve | evaluation_values_normal) | split
    | unit =>
      simp only [evalValue]
      repeat' first | exact constructing | (solve | evaluation_values_normal) | split
    | arr element count =>
      simp only [evalValue]
      repeat' first | exact constructing | (solve | evaluation_values_normal) | split
    | varr element =>
      simp only [evalValue]
      repeat' first | exact constructing | (solve | evaluation_values_normal) | split
    | grow element =>
      simp only [evalValue]
      repeat' first | exact constructing | (solve | evaluation_values_normal) | split
    | growshrink element =>
      simp only [evalValue]
      repeat' first | exact constructing | (solve | evaluation_values_normal) | split
    | limited element capacity =>
      simp only [evalValue]
      repeat' first | exact constructing | (solve | evaluation_values_normal) | split
    | ref mutability target =>
      simp only [evalValue]
      repeat' first | exact constructing | (solve | evaluation_values_normal) | split
    | tuple parts =>
      simp only [evalValue]
      repeat' first | exact constructing | (solve | evaluation_values_normal) | split
    | structT id fields =>
      simp only [evalValue]
      repeat' first | exact constructing | (solve | evaluation_values_normal) | split
    | slice mutability element =>
      cases element with
      | int integer =>
        cases integer <;> simp only [evalValue]
        all_goals evaluation_values_normal
      | bool =>
        simp only [evalValue]
        evaluation_values_normal
      | unit =>
        simp only [evalValue]
        evaluation_values_normal
      | arr element count =>
        simp only [evalValue]
        evaluation_values_normal
      | varr element =>
        simp only [evalValue]
        evaluation_values_normal
      | grow element =>
        simp only [evalValue]
        evaluation_values_normal
      | growshrink element =>
        simp only [evalValue]
        evaluation_values_normal
      | limited element capacity =>
        simp only [evalValue]
        evaluation_values_normal
      | ref mutability target =>
        simp only [evalValue]
        evaluation_values_normal
      | tuple parts =>
        simp only [evalValue]
        evaluation_values_normal
      | slice innerMutability innerElement =>
        simp only [evalValue]
        evaluation_values_normal

      | structT id fields =>
        simp only [evalValue]
        evaluation_values_normal

private theorem value_str_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (ty : Ty) (arguments : List PrintArg) (origin : Goose.Core.OriginId) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.str ty arguments origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.str ty arguments origin)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.str ty arguments origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    simp only [evalValue]
    apply controlFlow_suffix
    · apply controlFlow_constructLocal
      intro destination
      exact previous.build environment destination (.str ty arguments origin) (staticFuel + 1) enough
    · intro carrier; evaluation_values_normal

private theorem value_copy_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (ty : Ty) (source : Place) (origin : Goose.Core.OriginId) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.copy ty source origin) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.copy ty source origin)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.copy ty source origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : placeQueryBudget source + 1 ≤ staticFuel + 1 := enough
    simp only [evalValue]
    split
    · apply controlFlow_suffix
      · apply controlFlow_constructLocal
        intro destination
        exact previous.build environment destination (.copy ty source origin) (staticFuel + 1) enough
      · intro carrier; evaluation_values_normal
    · change ControlFlowAction environment.act (placeFlows staticFuel source) (fun _ => normalFlow) _
      apply controlFlow_suffix
      · exact previous.place environment source staticFuel (by omega)
      · intro location; evaluation_values_normal

private theorem value_values_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (operands : List Expr) (staticFuel : Nat) (enough : expressionQueryBudget (Expr.values operands) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.values operands)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (Expr.values operands)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionListQueryBudget operands + 1 ≤ staticFuel + 1 := enough
    cases operands with
    | nil =>
      have enoughList : 1 ≤ staticFuel := by change 1 + 1 ≤ staticFuel + 1 at enough; omega
      cases staticFuel with
      | zero => omega
      | succ staticFuel => simp only [evalValue]; exact controlFlow_pure _ _ _ (List.mem_singleton_self _)
    | cons operand rest =>
      cases rest with
      | nil =>
        have listBudget : expressionQueryBudget operand + 1 + 1 ≤ staticFuel := by
          change expressionQueryBudget operand + 1 + 1 + 1 ≤ staticFuel + 1 at enough
          omega
        cases staticFuel with
        | zero => omega
        | succ staticFuel =>
          change ControlFlowAction environment.act
            (continueFlows (expressionFlows staticFuel operand) (expressionsFlows staticFuel [])) (fun _ => normalFlow) _
          have empty : expressionsFlows staticFuel [] = [normalFlow] := by cases staticFuel <;> rfl
          rw [empty, continueFlows_normal_right]
          simp only [evalValue]
          exact previous.value environment operand staticFuel (by omega)
      | cons second rest => simp only [evalValue]; exact controlFlow_stop _ _ _

private theorem value_boolean_flows (fuel : Nat) (value : Bool) :
    expressionFlows fuel (.bool value) = [normalFlow] := by
  cases fuel <;> rfl

private theorem value_and_dynamic (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (left right : Expr) (staticFuel : Nat)
    (leftEnough : expressionQueryBudget left ≤ staticFuel)
    (rightEnough : expressionQueryBudget right ≤ staticFuel) :
    ControlFlowAction environment.act
      (continueFlows (expressionFlows staticFuel left) (normalFlow :: expressionFlows staticFuel right)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (.and left right)) := by
  simp only [evalValue]
  apply controlFlow_bind
  · exact previous.value environment left staticFuel leftEnough
  · intro leftValue
    apply controlFlow_prefix
    · evaluation_values_normal
    · intro boolean
      cases boolean with
      | false =>
        exact controlFlow_pure _ _ (Value.bool false) List.mem_cons_self
      | true =>
        apply controlFlow_mono (expressionFlows staticFuel right)
        · intro flow present; exact List.mem_cons_of_mem _ present
        · apply controlFlow_suffix
          · exact previous.value environment right staticFuel rightEnough
          · intro rightValue; evaluation_values_normal

private theorem value_and_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (left right : Expr) (staticFuel : Nat) (enough : expressionQueryBudget (.and left right) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (.and left right)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (.and left right)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget left + expressionQueryBudget right + 1 ≤ staticFuel + 1 := enough
    have leftEnough : expressionQueryBudget left ≤ staticFuel := by omega
    have rightEnough : expressionQueryBudget right ≤ staticFuel := by omega
    change ControlFlowAction environment.act
      (continueFlows (expressionFlows staticFuel left) (match (generalizing := false) left with
        | .bool false => [normalFlow]
        | .bool true => expressionFlows staticFuel right
        | _ => normalFlow :: expressionFlows staticFuel right)) (fun _ => normalFlow) _
    by_cases literal : ∃ boolean, left = .bool boolean
    · obtain ⟨boolean, rfl⟩ := literal
      rw [value_boolean_flows, continueFlows_normal_left]
      cases boolean with
      | false =>
        cases fuel with
        | zero => simp only [evalValue]; exact controlFlow_stop _ _ .timeout
        | succ fuel =>
          simp only [evalValue]
          exact controlFlow_pure _ _ (Value.bool false) (List.mem_singleton_self _)
      | true =>
        cases fuel with
        | zero => simp only [evalValue]; exact controlFlow_stop _ _ .timeout
        | succ fuel =>
          simp only [evalValue]
          change ControlFlowAction environment.act (expressionFlows staticFuel right) (fun _ => normalFlow)
            (do pure (Value.bool (← expectBool (← evalValue (fuel + 1) config environment right))))
          apply controlFlow_suffix
          · exact previous.value environment right staticFuel rightEnough
          · intro value; evaluation_values_normal
    · have shape : (match (generalizing := false) left with
          | .bool false => [normalFlow]
          | .bool true => expressionFlows staticFuel right
          | _ => normalFlow :: expressionFlows staticFuel right) = normalFlow :: expressionFlows staticFuel right := by
        cases left <;> try rfl
        case bool boolean => exact False.elim (literal ⟨boolean, rfl⟩)
      rw [shape]
      exact value_and_dynamic fuel config previous environment left right staticFuel leftEnough rightEnough

private theorem value_or_dynamic (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (left right : Expr) (staticFuel : Nat)
    (leftEnough : expressionQueryBudget left ≤ staticFuel)
    (rightEnough : expressionQueryBudget right ≤ staticFuel) :
    ControlFlowAction environment.act
      (continueFlows (expressionFlows staticFuel left) (normalFlow :: expressionFlows staticFuel right)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (.or left right)) := by
  simp only [evalValue]
  apply controlFlow_bind
  · exact previous.value environment left staticFuel leftEnough
  · intro leftValue
    apply controlFlow_prefix
    · evaluation_values_normal
    · intro boolean
      cases boolean with
      | false =>
        apply controlFlow_mono (expressionFlows staticFuel right)
        · intro flow present; exact List.mem_cons_of_mem _ present
        · apply controlFlow_suffix
          · exact previous.value environment right staticFuel rightEnough
          · intro rightValue; evaluation_values_normal
      | true =>
        exact controlFlow_pure _ _ (Value.bool true) List.mem_cons_self

private theorem value_or_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (left right : Expr) (staticFuel : Nat) (enough : expressionQueryBudget (.or left right) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (.or left right)) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment (.or left right)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget left + expressionQueryBudget right + 1 ≤ staticFuel + 1 := enough
    have leftEnough : expressionQueryBudget left ≤ staticFuel := by omega
    have rightEnough : expressionQueryBudget right ≤ staticFuel := by omega
    change ControlFlowAction environment.act
      (continueFlows (expressionFlows staticFuel left) (match (generalizing := false) left with
        | .bool true => [normalFlow]
        | .bool false => expressionFlows staticFuel right
        | _ => normalFlow :: expressionFlows staticFuel right)) (fun _ => normalFlow) _
    by_cases literal : ∃ boolean, left = .bool boolean
    · obtain ⟨boolean, rfl⟩ := literal
      rw [value_boolean_flows, continueFlows_normal_left]
      cases boolean with
      | false =>
        cases fuel with
        | zero => simp only [evalValue]; exact controlFlow_stop _ _ .timeout
        | succ fuel =>
          simp only [evalValue]
          change ControlFlowAction environment.act (expressionFlows staticFuel right) (fun _ => normalFlow)
            (do pure (Value.bool (← expectBool (← evalValue (fuel + 1) config environment right))))
          apply controlFlow_suffix
          · exact previous.value environment right staticFuel rightEnough
          · intro value; evaluation_values_normal
      | true =>
        cases fuel with
        | zero => simp only [evalValue]; exact controlFlow_stop _ _ .timeout
        | succ fuel =>
          simp only [evalValue]
          exact controlFlow_pure _ _ (Value.bool true) (List.mem_singleton_self _)
    · have shape : (match (generalizing := false) left with
          | .bool true => [normalFlow]
          | .bool false => expressionFlows staticFuel right
          | _ => normalFlow :: expressionFlows staticFuel right) = normalFlow :: expressionFlows staticFuel right := by
        cases left <;> try rfl
        case bool boolean => exact False.elim (literal ⟨boolean, rfl⟩)
      rw [shape]
      exact value_or_dynamic fuel config previous environment left right staticFuel leftEnough rightEnough

theorem evaluationControl_value_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (input : Expr) (staticFuel : Nat) (enough : expressionQueryBudget input ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel input) (fun _ => normalFlow)
      (evalValue (fuel + 1) config environment input) := by
  cases input with
  | lit t n => exact value_lit_succ fuel config environment t n staticFuel enough
  | bool b => exact value_bool_succ fuel config environment b staticFuel enough
  | read p => exact value_read_succ fuel config previous environment p staticFuel enough
  | ref m p => exact value_ref_succ fuel config previous environment m p staticFuel enough
  | slice m v lo hi org => exact value_slice_succ fuel config previous environment m v lo hi org staticFuel enough
  | len v => exact value_len_succ fuel config previous environment v staticFuel enough
  | un op e org => exact value_un_succ fuel config previous environment op e org staticFuel enough
  | bin op a b org => exact value_bin_succ fuel config previous environment op a b org staticFuel enough
  | cmp op a b => exact value_cmp_succ fuel config previous environment op a b staticFuel enough
  | and a b => exact value_and_succ fuel config previous environment a b staticFuel enough
  | or a b => exact value_or_succ fuel config previous environment a b staticFuel enough
  | not e => exact value_not_succ fuel config previous environment e staticFuel enough
  | conv k target e org => exact value_conv_succ fuel config previous environment k target e org staticFuel enough
  | call c args org => exact value_call_succ fuel config previous environment c args org staticFuel enough
  | push owner e org => exact value_push_succ fuel config previous environment owner e org staticFuel enough
  | pop owner org => exact value_pop_succ fuel config previous environment owner org staticFuel enough
  | ifE c thenB elseB org => exact value_ifE_succ fuel config previous environment c thenB elseB org staticFuel enough
  | blockE b org => exact value_blockE_succ fuel config previous environment b org staticFuel enough
  | arrLit t es org => exact value_arrLit_succ fuel config previous environment t es org staticFuel enough
  | fill t e org => exact value_fill_succ fuel config previous environment t e org staticFuel enough
  | structLit t es => exact value_structLit_succ fuel config previous environment t es staticFuel enough
  | bytes t data org => exact value_bytes_succ fuel config previous environment t data org staticFuel enough
  | str t args org => exact value_str_succ fuel config previous environment t args org staticFuel enough
  | copy t source org => exact value_copy_succ fuel config previous environment t source org staticFuel enough
  | resultLocal var org => exact value_resultLocal_succ fuel config environment var org staticFuel enough
  | values operands => exact value_values_succ fuel config previous environment operands staticFuel enough

#print axioms evaluationControl_value_succ

end Goose.Proofs.ConstructionDelivery

import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationProduceLoops
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationProduceControl

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

elab "evaluation_produce_build_start " destination:ident : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| simp only [buildExpr]))
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply controlFlow_prefix))
  let goals ← Lean.Elab.Tactic.getGoals
  let head :: tail :: remaining := goals | throwError "expected renewal and destination body"
  Lean.Elab.Tactic.setGoals [head]
  Lean.Elab.Tactic.evalTactic (← `(tactic| evaluation_produce_normal))
  unless (← Lean.Elab.Tactic.getGoals).isEmpty do throwError "unproved renewal action"
  Lean.Elab.Tactic.setGoals (tail :: remaining)
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro $destination:ident))
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply controlFlow_protectDestination))

private theorem produce_buildValue (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (expression : Expr) (staticFuel : Nat)
    (enough : expressionQueryBudget expression ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel expression) (fun _ => normalFlow) (do
      let value ← evalValue fuel config environment expression
      copyValue fuel config.layout destination value (expressionOrigin expression) none) := by
  apply controlFlow_suffix
  · exact previous.value environment expression staticFuel enough
  · intro value
    evaluation_produce_normal

private theorem build_lit_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (t : Goose.Core.IntTy) (n : Int) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.lit t n) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.lit t n)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.lit t n)) := by
  evaluation_produce_build_start destination
  exact produce_buildValue fuel config previous environment destination (Expr.lit t n) staticFuel enough

private theorem build_bool_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (b : Bool) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.bool b) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.bool b)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.bool b)) := by
  evaluation_produce_build_start destination
  exact produce_buildValue fuel config previous environment destination (Expr.bool b) staticFuel enough

private theorem build_read_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (p : Place) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.read p) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.read p)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.read p)) := by
  evaluation_produce_build_start destination
  exact produce_buildValue fuel config previous environment destination (Expr.read p) staticFuel enough

private theorem build_ref_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (m : Goose.Core.Mutability) (p : Place) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.ref m p) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.ref m p)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.ref m p)) := by
  evaluation_produce_build_start destination
  exact produce_buildValue fuel config previous environment destination (Expr.ref m p) staticFuel enough

private theorem build_slice_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (m : Goose.Core.Mutability) (v : View) (lo hi : Bound) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.slice m v lo hi org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.slice m v lo hi org)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.slice m v lo hi org)) := by
  evaluation_produce_build_start destination
  exact produce_buildValue fuel config previous environment destination (Expr.slice m v lo hi org) staticFuel enough

private theorem build_len_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (v : View) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.len v) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.len v)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.len v)) := by
  evaluation_produce_build_start destination
  exact produce_buildValue fuel config previous environment destination (Expr.len v) staticFuel enough

private theorem build_un_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (op : Goose.Core.UnOp) (e : Expr) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.un op e org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.un op e org)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.un op e org)) := by
  evaluation_produce_build_start destination
  exact produce_buildValue fuel config previous environment destination (Expr.un op e org) staticFuel enough

private theorem build_bin_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (op : Goose.Core.BinOp) (a b : Expr) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.bin op a b org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.bin op a b org)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.bin op a b org)) := by
  evaluation_produce_build_start destination
  exact produce_buildValue fuel config previous environment destination (Expr.bin op a b org) staticFuel enough

private theorem build_cmp_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (op : Goose.Core.CmpOp) (a b : Expr) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.cmp op a b) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.cmp op a b)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.cmp op a b)) := by
  evaluation_produce_build_start destination
  exact produce_buildValue fuel config previous environment destination (Expr.cmp op a b) staticFuel enough

private theorem build_and_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (a b : Expr) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.and a b) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.and a b)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.and a b)) := by
  evaluation_produce_build_start destination
  exact produce_buildValue fuel config previous environment destination (Expr.and a b) staticFuel enough

private theorem build_or_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (a b : Expr) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.or a b) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.or a b)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.or a b)) := by
  evaluation_produce_build_start destination
  exact produce_buildValue fuel config previous environment destination (Expr.or a b) staticFuel enough

private theorem build_not_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (e : Expr) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.not e) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.not e)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.not e)) := by
  evaluation_produce_build_start destination
  exact produce_buildValue fuel config previous environment destination (Expr.not e) staticFuel enough

private theorem build_conv_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (k : Goose.Core.ConvKind) (target : Ty) (e : Expr) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.conv k target e org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.conv k target e org)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.conv k target e org)) := by
  evaluation_produce_build_start destination
  exact produce_buildValue fuel config previous environment destination (Expr.conv k target e org) staticFuel enough

private theorem build_call_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (c : Goose.Core.ContextId) (args : List Arg) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.call c args org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.call c args org)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.call c args org)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    evaluation_produce_build_start destination
    have argumentsEnough : argumentsQueryBudget args ≤ staticFuel := by
      change argumentsQueryBudget args + 1 ≤ staticFuel + 1 at enough
      omega
    apply controlFlow_suffix
    · exact previous.call environment c args [.construct destination] org staticFuel argumentsEnough
    · intro carriers
      evaluation_produce_normal

private theorem build_push_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (owner : Place) (e : Expr) (org : Option Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.push owner e org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.push owner e org)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.push owner e org)) := by
  evaluation_produce_build_start destination
  exact produce_buildValue fuel config previous environment destination (Expr.push owner e org) staticFuel enough

private theorem build_pop_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (owner : Place) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.pop owner org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.pop owner org)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.pop owner org)) := by
  evaluation_produce_build_start destination
  exact produce_buildValue fuel config previous environment destination (Expr.pop owner org) staticFuel enough

private theorem build_ifE_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (c : Expr) (thenB elseB : Block) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.ifE c thenB elseB org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.ifE c thenB elseB org)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.ifE c thenB elseB org)) := by
  evaluation_produce_build_start destination
  exact evaluationControl_ifResultBlock fuel config previous environment [.construct destination] c thenB elseB org staticFuel enough (fun _ => ())

private theorem build_blockE_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (b : Block) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.blockE b org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.blockE b org)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.blockE b org)) := by
  evaluation_produce_build_start destination
  exact evaluationControl_buildBlock fuel config previous environment destination b org staticFuel enough

private theorem build_arrLit_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (t : Ty) (es : List Expr) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.arrLit t es org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.arrLit t es org)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.arrLit t es org)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    evaluation_produce_build_start destination
    have operandsEnough : expressionListQueryBudget es ≤ staticFuel := by
      change expressionListQueryBudget es + 1 ≤ staticFuel + 1 at enough
      omega
    apply controlFlow_prefix
    · evaluation_produce_normal
    · intro pending
      split
      next element found =>
        apply controlFlow_suffix
        · exact evaluationControl_buildElements fuel config previous environment destination element es staticFuel operandsEnough PUnit.unit
        · intro ignored
          evaluation_produce_normal
      next => exact controlFlow_stop _ _ _

private theorem build_fill_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (t : Ty) (e : Expr) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.fill t e org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.fill t e org)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.fill t e org)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    have operandEnough : expressionQueryBudget e ≤ staticFuel := by
      change expressionQueryBudget e + 1 ≤ staticFuel + 1 at enough
      omega
    cases t <;> evaluation_produce_build_start destination
    all_goals try exact controlFlow_stop _ _ _
    split
    · apply controlFlow_prefix
      · evaluation_produce_normal
      · intro source
        apply controlFlow_suffix
        · exact previous.build environment source e staticFuel operandEnough
        · intro ignored
          evaluation_produce_normal
    · apply controlFlow_suffix
      · exact previous.value environment e staticFuel operandEnough
      · intro value
        evaluation_produce_normal


private theorem build_structLit_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (t : Ty) (es : List Expr) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.structLit t es) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.structLit t es)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.structLit t es)) := by
  evaluation_produce_build_start destination
  exact produce_buildValue fuel config previous environment destination (Expr.structLit t es) staticFuel enough

private theorem build_bytes_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (t : Ty) (data : List UInt8) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.bytes t data org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.bytes t data org)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.bytes t data org)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    evaluation_produce_build_start destination
    evaluation_produce_normal

private theorem build_str_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (t : Ty) (args : List PrintArg) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.str t args org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.str t args org)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.str t args org)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    evaluation_produce_build_start destination
    have argumentsEnough : printArgumentsQueryBudget args ≤ staticFuel := by
      change printArgumentsQueryBudget args + 1 ≤ staticFuel + 1 at enough
      omega
    apply controlFlow_suffix
    · exact evaluationControl_buildPrintArguments fuel config previous environment destination org args staticFuel argumentsEnough PUnit.unit
    · intro ignored
      evaluation_produce_normal

private theorem build_copy_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (t : Ty) (source : Place) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.copy t source org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.copy t source org)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.copy t source org)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    evaluation_produce_build_start destination
    have placeEnough : placeQueryBudget source ≤ staticFuel := by
      change placeQueryBudget source + 1 ≤ staticFuel + 1 at enough
      omega
    apply controlFlow_suffix
    · exact previous.place environment source staticFuel placeEnough
    · intro location
      evaluation_produce_normal

private theorem build_resultLocal_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (var : Goose.Core.VarId) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.resultLocal var org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.resultLocal var org)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.resultLocal var org)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    evaluation_produce_build_start destination
    evaluation_produce_normal

private theorem build_values_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (operands : List Expr) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.values operands) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.values operands)) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming (Expr.values operands)) := by
  cases operands with
  | nil =>
    evaluation_produce_build_start destination
    exact produce_buildValue fuel config previous environment destination (.values []) staticFuel enough
  | cons operand rest =>
    cases rest with
    | cons next rest =>
      evaluation_produce_build_start destination
      exact produce_buildValue fuel config previous environment destination (.values (operand :: next :: rest)) staticFuel enough
    | nil =>
      cases staticFuel with
      | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
      | succ staticFuel =>
        cases staticFuel with
        | zero => change expressionQueryBudget operand + 1 + 1 + 1 ≤ 1 at enough; omega
        | succ staticFuel =>
          have operandEnough : expressionQueryBudget operand ≤ staticFuel := by
            change expressionQueryBudget operand + 1 + 1 + 1 ≤ staticFuel + 1 + 1 at enough
            omega
          have emptyFlow : expressionsFlows staticFuel ([] : List Expr) = [normalFlow] := by cases staticFuel <;> rfl
          evaluation_produce_build_start destination
          change ControlFlowAction environment.act
            (continueFlows (expressionFlows staticFuel operand) (expressionsFlows staticFuel [])) (fun _ => normalFlow) _
          rw [emptyFlow, continueFlows_normal_right]
          exact previous.build environment destination operand staticFuel operandEnough

theorem evaluationControl_build_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (expression : Expr) (staticFuel : Nat)
    (enough : expressionQueryBudget expression ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel expression) (fun _ => normalFlow)
      (buildExpr (fuel + 1) config environment incoming expression) := by
  cases expression with
  | lit t n => exact build_lit_succ fuel config previous environment incoming t n staticFuel enough
  | bool b => exact build_bool_succ fuel config previous environment incoming b staticFuel enough
  | read p => exact build_read_succ fuel config previous environment incoming p staticFuel enough
  | ref m p => exact build_ref_succ fuel config previous environment incoming m p staticFuel enough
  | slice m v lo hi org => exact build_slice_succ fuel config previous environment incoming m v lo hi org staticFuel enough
  | len v => exact build_len_succ fuel config previous environment incoming v staticFuel enough
  | un op e org => exact build_un_succ fuel config previous environment incoming op e org staticFuel enough
  | bin op a b org => exact build_bin_succ fuel config previous environment incoming op a b org staticFuel enough
  | cmp op a b => exact build_cmp_succ fuel config previous environment incoming op a b staticFuel enough
  | and a b => exact build_and_succ fuel config previous environment incoming a b staticFuel enough
  | or a b => exact build_or_succ fuel config previous environment incoming a b staticFuel enough
  | not e => exact build_not_succ fuel config previous environment incoming e staticFuel enough
  | conv k target e org => exact build_conv_succ fuel config previous environment incoming k target e org staticFuel enough
  | call c args org => exact build_call_succ fuel config previous environment incoming c args org staticFuel enough
  | push owner e org => exact build_push_succ fuel config previous environment incoming owner e org staticFuel enough
  | pop owner org => exact build_pop_succ fuel config previous environment incoming owner org staticFuel enough
  | ifE c thenB elseB org => exact build_ifE_succ fuel config previous environment incoming c thenB elseB org staticFuel enough
  | blockE b org => exact build_blockE_succ fuel config previous environment incoming b org staticFuel enough
  | arrLit t es org => exact build_arrLit_succ fuel config previous environment incoming t es org staticFuel enough
  | fill t e org => exact build_fill_succ fuel config previous environment incoming t e org staticFuel enough
  | structLit t es => exact build_structLit_succ fuel config previous environment incoming t es staticFuel enough
  | bytes t data org => exact build_bytes_succ fuel config previous environment incoming t data org staticFuel enough
  | str t args org => exact build_str_succ fuel config previous environment incoming t args org staticFuel enough
  | copy t source org => exact build_copy_succ fuel config previous environment incoming t source org staticFuel enough
  | resultLocal var org => exact build_resultLocal_succ fuel config previous environment incoming var org staticFuel enough
  | values operands => exact build_values_succ fuel config previous environment incoming operands staticFuel enough

#print axioms evaluationControl_build_succ

end Goose.Proofs.ConstructionDelivery

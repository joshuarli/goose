import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationFramesProducers

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

private theorem buildExpr_lit_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (t : Goose.Core.IntTy) (n : Int) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.lit t n)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_bool_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (b : Bool) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.bool b)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_read_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (p : Place) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.read p)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_ref_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (m : Goose.Core.Mutability) (p : Place) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.ref m p)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_slice_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (m : Goose.Core.Mutability) (v : View) (lo hi : Bound) (org : Goose.Core.OriginId) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.slice m v lo hi org)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_len_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (v : View) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.len v)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_un_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (op : Goose.Core.UnOp) (e : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.un op e org)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_bin_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (op : Goose.Core.BinOp) (a b : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.bin op a b org)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_cmp_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (op : Goose.Core.CmpOp) (a b : Expr) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.cmp op a b)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_and_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (a b : Expr) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.and a b)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_or_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (a b : Expr) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.or a b)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_not_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (e : Expr) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.not e)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_conv_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (k : Goose.Core.ConvKind) (target : Ty) (e : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.conv k target e org)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_call_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (c : Goose.Core.ContextId) (args : List Arg) (org : Goose.Core.OriginId) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.call c args org)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_push_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (owner : Place) (e : Expr) (org : Option Goose.Core.OriginId) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.push owner e org)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_pop_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (owner : Place) (org : Goose.Core.OriginId) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.pop owner org)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_ifE_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (c : Expr) (thenB elseB : Block) (org : Goose.Core.OriginId) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.ifE c thenB elseB org)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_blockE_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (b : Block) (org : Goose.Core.OriginId) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.blockE b org)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_arrLit_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (t : Ty) (es : List Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.arrLit t es org)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_fill_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (t : Ty) (e : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.fill t e org)) := by
  cases t <;> simp only [buildExpr]
  all_goals evaluation_frame previous

private theorem buildExpr_structLit_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (t : Ty) (es : List Expr) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.structLit t es)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_bytes_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (t : Ty) (data : List UInt8) (org : Goose.Core.OriginId) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.bytes t data org)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_str_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (t : Ty) (args : List PrintArg) (org : Goose.Core.OriginId) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.str t args org)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_copy_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (t : Ty) (source : Place) (org : Goose.Core.OriginId) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.copy t source org)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_resultLocal_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (var : Goose.Core.VarId) (org : Goose.Core.OriginId) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.resultLocal var org)) := by
  simp only [buildExpr]
  evaluation_frame previous

private theorem buildExpr_values_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (operands : List Expr) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination (Expr.values operands)) := by
  cases operands with
  | nil =>
    simp only [buildExpr]
    evaluation_frame previous
  | cons expression operands =>
    cases operands <;> simp only [buildExpr]
    all_goals evaluation_frame previous

theorem buildExpr_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (input : Expr) :
    BreakFrameAction (buildExpr (fuel + 1) config environment destination input) := by
  cases input with
  | lit t n => exact buildExpr_lit_breakFrame_succ fuel config previous environment destination t n
  | bool b => exact buildExpr_bool_breakFrame_succ fuel config previous environment destination b
  | read p => exact buildExpr_read_breakFrame_succ fuel config previous environment destination p
  | ref m p => exact buildExpr_ref_breakFrame_succ fuel config previous environment destination m p
  | slice m v lo hi org => exact buildExpr_slice_breakFrame_succ fuel config previous environment destination m v lo hi org
  | len v => exact buildExpr_len_breakFrame_succ fuel config previous environment destination v
  | un op e org => exact buildExpr_un_breakFrame_succ fuel config previous environment destination op e org
  | bin op a b org => exact buildExpr_bin_breakFrame_succ fuel config previous environment destination op a b org
  | cmp op a b => exact buildExpr_cmp_breakFrame_succ fuel config previous environment destination op a b
  | and a b => exact buildExpr_and_breakFrame_succ fuel config previous environment destination a b
  | or a b => exact buildExpr_or_breakFrame_succ fuel config previous environment destination a b
  | not e => exact buildExpr_not_breakFrame_succ fuel config previous environment destination e
  | conv k target e org => exact buildExpr_conv_breakFrame_succ fuel config previous environment destination k target e org
  | call c args org => exact buildExpr_call_breakFrame_succ fuel config previous environment destination c args org
  | push owner e org => exact buildExpr_push_breakFrame_succ fuel config previous environment destination owner e org
  | pop owner org => exact buildExpr_pop_breakFrame_succ fuel config previous environment destination owner org
  | ifE c thenB elseB org => exact buildExpr_ifE_breakFrame_succ fuel config previous environment destination c thenB elseB org
  | blockE b org => exact buildExpr_blockE_breakFrame_succ fuel config previous environment destination b org
  | arrLit t es org => exact buildExpr_arrLit_breakFrame_succ fuel config previous environment destination t es org
  | fill t e org => exact buildExpr_fill_breakFrame_succ fuel config previous environment destination t e org
  | structLit t es => exact buildExpr_structLit_breakFrame_succ fuel config previous environment destination t es
  | bytes t data org => exact buildExpr_bytes_breakFrame_succ fuel config previous environment destination t data org
  | str t args org => exact buildExpr_str_breakFrame_succ fuel config previous environment destination t args org
  | copy t source org => exact buildExpr_copy_breakFrame_succ fuel config previous environment destination t source org
  | resultLocal var org => exact buildExpr_resultLocal_breakFrame_succ fuel config previous environment destination var org
  | values operands => exact buildExpr_values_breakFrame_succ fuel config previous environment destination operands

end Goose.Proofs.ConstructionDelivery

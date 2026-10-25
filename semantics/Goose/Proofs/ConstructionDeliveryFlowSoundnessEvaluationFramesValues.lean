import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationFramesProducers

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

private theorem evalValue_lit_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (t : Goose.Core.IntTy) (n : Int) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.lit t n)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_bool_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (b : Bool) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.bool b)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_read_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (p : Place) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.read p)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_ref_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (m : Goose.Core.Mutability) (p : Place) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.ref m p)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_slice_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (m : Goose.Core.Mutability) (v : View) (lo hi : Bound) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.slice m v lo hi org)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_len_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (v : View) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.len v)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_un_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (op : Goose.Core.UnOp) (e : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.un op e org)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_bin_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (op : Goose.Core.BinOp) (a b : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.bin op a b org)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_cmp_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (op : Goose.Core.CmpOp) (a b : Expr) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.cmp op a b)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_and_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (a b : Expr) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.and a b)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_or_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (a b : Expr) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.or a b)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_not_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (e : Expr) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.not e)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_conv_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (k : Goose.Core.ConvKind) (target : Ty) (e : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.conv k target e org)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_call_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (c : Goose.Core.ContextId) (args : List Arg) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.call c args org)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_push_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (owner : Place) (e : Expr) (org : Option Goose.Core.OriginId) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.push owner e org)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_pop_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (owner : Place) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.pop owner org)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_ifE_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (c : Expr) (thenB elseB : Block) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.ifE c thenB elseB org)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_blockE_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (b : Block) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.blockE b org)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_arrLit_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (t : Ty) (es : List Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.arrLit t es org)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_fill_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (t : Ty) (e : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.fill t e org)) := by
  cases t <;> simp only [evalValue]
  all_goals evaluation_frame previous

private theorem evalValue_structLit_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (t : Ty) (es : List Expr) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.structLit t es)) := by
  cases t <;> simp only [evalValue]
  all_goals evaluation_frame previous

private theorem evalValue_bytes_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (t : Ty) (data : List UInt8) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.bytes t data org)) := by
  cases t <;> try simp only [evalValue]
  all_goals evaluation_frame previous
  case slice mutability element =>
    cases element <;> try simp only [evalValue]
    all_goals evaluation_frame previous
    case int ty =>
      cases ty <;> simp only [evalValue]
      all_goals evaluation_frame previous

private theorem evalValue_str_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (t : Ty) (args : List PrintArg) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.str t args org)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_copy_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (t : Ty) (source : Place) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.copy t source org)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_resultLocal_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (var : Goose.Core.VarId) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.resultLocal var org)) := by
  simp only [evalValue]
  evaluation_frame previous

private theorem evalValue_values_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (operands : List Expr) :
    BreakFrameAction (evalValue (fuel + 1) config environment (Expr.values operands)) := by
  cases operands with
  | nil => simpa only [evalValue] using breakFrame_pure Value.unit
  | cons expression operands =>
    cases operands <;> simp only [evalValue]
    all_goals evaluation_frame previous

theorem evalValue_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (input : Expr) :
    BreakFrameAction (evalValue (fuel + 1) config environment input) := by
  cases input with
  | lit t n => exact evalValue_lit_breakFrame_succ fuel config previous environment t n
  | bool b => exact evalValue_bool_breakFrame_succ fuel config previous environment b
  | read p => exact evalValue_read_breakFrame_succ fuel config previous environment p
  | ref m p => exact evalValue_ref_breakFrame_succ fuel config previous environment m p
  | slice m v lo hi org => exact evalValue_slice_breakFrame_succ fuel config previous environment m v lo hi org
  | len v => exact evalValue_len_breakFrame_succ fuel config previous environment v
  | un op e org => exact evalValue_un_breakFrame_succ fuel config previous environment op e org
  | bin op a b org => exact evalValue_bin_breakFrame_succ fuel config previous environment op a b org
  | cmp op a b => exact evalValue_cmp_breakFrame_succ fuel config previous environment op a b
  | and a b => exact evalValue_and_breakFrame_succ fuel config previous environment a b
  | or a b => exact evalValue_or_breakFrame_succ fuel config previous environment a b
  | not e => exact evalValue_not_breakFrame_succ fuel config previous environment e
  | conv k target e org => exact evalValue_conv_breakFrame_succ fuel config previous environment k target e org
  | call c args org => exact evalValue_call_breakFrame_succ fuel config previous environment c args org
  | push owner e org => exact evalValue_push_breakFrame_succ fuel config previous environment owner e org
  | pop owner org => exact evalValue_pop_breakFrame_succ fuel config previous environment owner org
  | ifE c thenB elseB org => exact evalValue_ifE_breakFrame_succ fuel config previous environment c thenB elseB org
  | blockE b org => exact evalValue_blockE_breakFrame_succ fuel config previous environment b org
  | arrLit t es org => exact evalValue_arrLit_breakFrame_succ fuel config previous environment t es org
  | fill t e org => exact evalValue_fill_breakFrame_succ fuel config previous environment t e org
  | structLit t es => exact evalValue_structLit_breakFrame_succ fuel config previous environment t es
  | bytes t data org => exact evalValue_bytes_breakFrame_succ fuel config previous environment t data org
  | str t args org => exact evalValue_str_breakFrame_succ fuel config previous environment t args org
  | copy t source org => exact evalValue_copy_breakFrame_succ fuel config previous environment t source org
  | resultLocal var org => exact evalValue_resultLocal_breakFrame_succ fuel config previous environment var org
  | values operands => exact evalValue_values_breakFrame_succ fuel config previous environment operands

end Goose.Proofs.ConstructionDelivery

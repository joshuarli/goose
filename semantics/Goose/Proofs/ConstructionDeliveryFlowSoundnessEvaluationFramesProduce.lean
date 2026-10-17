import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationFramesProducers

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

private theorem evalProduce_lit_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (t : Goose.Core.IntTy) (n : Int) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.lit t n)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_bool_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (b : Bool) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.bool b)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_read_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (p : Place) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.read p)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_ref_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (m : Goose.Core.Mutability) (p : Place) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.ref m p)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_slice_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (m : Goose.Core.Mutability) (v : View) (lo hi : Bound) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.slice m v lo hi org)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_len_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (v : View) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.len v)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_un_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (op : Goose.Core.UnOp) (e : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.un op e org)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_bin_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (op : Goose.Core.BinOp) (a b : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.bin op a b org)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_cmp_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (op : Goose.Core.CmpOp) (a b : Expr) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.cmp op a b)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_and_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (a b : Expr) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.and a b)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_or_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (a b : Expr) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.or a b)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_not_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (e : Expr) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.not e)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_conv_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (k : Goose.Core.ConvKind) (target : Ty) (e : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.conv k target e org)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_call_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (c : Goose.Core.ContextId) (args : List Arg) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.call c args org)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_push_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (owner : Place) (e : Expr) (org : Option Goose.Core.OriginId) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.push owner e org)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_pop_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (owner : Place) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.pop owner org)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_ifE_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (c : Expr) (thenB elseB : Block) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.ifE c thenB elseB org)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_blockE_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (b : Block) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.blockE b org)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_arrLit_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (es : List Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.arrLit t es org)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_fill_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (e : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.fill t e org)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_structLit_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (es : List Expr) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.structLit t es)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_bytes_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (data : List UInt8) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.bytes t data org)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_str_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (args : List PrintArg) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.str t args org)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_copy_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (source : Place) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.copy t source org)) := by
  simp only [evalProduce]
  evaluation_frame previous

private theorem evalProduce_resultLocal_tail_breakFrame (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (selected planned : List Channel) (localVar : Goose.Core.VarId) (origin : Goose.Core.OriginId) :
    BreakFrameAction (match selected with
      | [.construct destination] => do
        let .stored stored ← readLoc fuel config.layout ⟨← rootOf environment localVar, []⟩ | fault .shape
        let named ← match planned with
          | [.completion token] => prepareNamedCarrierAt origin token destination stored
          | _ => prepareNamedCarrier origin destination stored
        match named with
        | some carrier => pure [carrier]
        | none =>
          buildExpr fuel config environment destination (.resultLocal localVar origin)
          pure [.completed (← completedReceivingDestination destination)]
      | [] => do let _ ← evalValue fuel config environment (.resultLocal localVar origin); pure []
      | [.register _] => do pure [.register (← evalValue fuel config environment (.resultLocal localVar origin))]
      | _ => fault .arity) := by
  evaluation_frame previous

private theorem evalProduce_resultLocal_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (var : Goose.Core.VarId) (org : Goose.Core.OriginId) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.resultLocal var org)) := by
  simp only [evalProduce]
  apply breakFrame_bind
  · apply breakFrame_listMapM
    intro channel
    cases channel <;> evaluation_frame_basic
  · intro planned
    apply breakFrame_bind
    · apply breakFrame_listMapM
      intro channel
      exact breakFrame_selectCompletionChannel _ _ _
    · intro selected
      exact evalProduce_resultLocal_tail_breakFrame fuel config previous environment selected planned var org

private theorem evalProduce_values_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (operands : List Expr) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels (Expr.values operands)) := by
  simp only [evalProduce]
  evaluation_frame previous

theorem evalProduce_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (input : Expr) :
    BreakFrameAction (evalProduce (fuel + 1) config environment channels input) := by
  cases input with
  | lit t n => exact evalProduce_lit_breakFrame_succ fuel config previous environment channels t n
  | bool b => exact evalProduce_bool_breakFrame_succ fuel config previous environment channels b
  | read p => exact evalProduce_read_breakFrame_succ fuel config previous environment channels p
  | ref m p => exact evalProduce_ref_breakFrame_succ fuel config previous environment channels m p
  | slice m v lo hi org => exact evalProduce_slice_breakFrame_succ fuel config previous environment channels m v lo hi org
  | len v => exact evalProduce_len_breakFrame_succ fuel config previous environment channels v
  | un op e org => exact evalProduce_un_breakFrame_succ fuel config previous environment channels op e org
  | bin op a b org => exact evalProduce_bin_breakFrame_succ fuel config previous environment channels op a b org
  | cmp op a b => exact evalProduce_cmp_breakFrame_succ fuel config previous environment channels op a b
  | and a b => exact evalProduce_and_breakFrame_succ fuel config previous environment channels a b
  | or a b => exact evalProduce_or_breakFrame_succ fuel config previous environment channels a b
  | not e => exact evalProduce_not_breakFrame_succ fuel config previous environment channels e
  | conv k target e org => exact evalProduce_conv_breakFrame_succ fuel config previous environment channels k target e org
  | call c args org => exact evalProduce_call_breakFrame_succ fuel config previous environment channels c args org
  | push owner e org => exact evalProduce_push_breakFrame_succ fuel config previous environment channels owner e org
  | pop owner org => exact evalProduce_pop_breakFrame_succ fuel config previous environment channels owner org
  | ifE c thenB elseB org => exact evalProduce_ifE_breakFrame_succ fuel config previous environment channels c thenB elseB org
  | blockE b org => exact evalProduce_blockE_breakFrame_succ fuel config previous environment channels b org
  | arrLit t es org => exact evalProduce_arrLit_breakFrame_succ fuel config previous environment channels t es org
  | fill t e org => exact evalProduce_fill_breakFrame_succ fuel config previous environment channels t e org
  | structLit t es => exact evalProduce_structLit_breakFrame_succ fuel config previous environment channels t es
  | bytes t data org => exact evalProduce_bytes_breakFrame_succ fuel config previous environment channels t data org
  | str t args org => exact evalProduce_str_breakFrame_succ fuel config previous environment channels t args org
  | copy t source org => exact evalProduce_copy_breakFrame_succ fuel config previous environment channels t source org
  | resultLocal var org => exact evalProduce_resultLocal_breakFrame_succ fuel config previous environment channels var org
  | values operands => exact evalProduce_values_breakFrame_succ fuel config previous environment channels operands

end Goose.Proofs.ConstructionDelivery

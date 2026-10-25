import Goose.Proofs.ExitExecutionActivationChannelsValues

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem evalProduce_blockE_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (block : Block) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.blockE block origin)) := by
  simp only [evalProduce]
  activation_channels_helper_eval_core previousFresh previous
  apply preservesActivationChannels_withBreakTarget
  · apply preservesActivationChannels_bind
    · exact previous.resultBlock _ _ _
    · exact previousFresh.resultBlock _ _ _
    · intro result
      cases result with
      | mk flow carriers =>
        cases flow with
        | normal _ => exact preservesActivationChannels_pure _
        | breaking _ | continuing => exact preservesActivationChannels_fault _
  · apply preservesFresh_bind
    · exact previousFresh.resultBlock _ _ _
    · intro result
      cases result with
      | mk flow carriers =>
        cases flow with
        | normal _ => exact preservesFresh_pure _
        | breaking _ | continuing => exact preservesFresh_stop _
  · intro kind
    cases kind with
    | breakValue carriers =>
      simp only [bind, pure]
      apply preservesActivationChannels_bind
      · exact preservesActivationChannels_landCarriersInto config origin _ carriers
      · exact preservesFresh_landCarriersInto origin _ carriers
      · intro _; exact preservesActivationChannels_pure _
    | continueLoop => exact preservesActivationChannels_fault _

private theorem evalProduce_lit_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (ty : Goose.Core.IntTy) (value : Int) :
    PreservesActivationChannels (evalProduce (fuel + 1) config environment channels (.lit ty value)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_bool_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (value : Bool) :
    PreservesActivationChannels (evalProduce (fuel + 1) config environment channels (.bool value)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_read_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (place : Place) :
    PreservesActivationChannels (evalProduce (fuel + 1) config environment channels (.read place)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_ref_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (mutability : Goose.Core.Mutability)
    (place : Place) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.ref mutability place)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_slice_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (mutability : Goose.Core.Mutability)
    (view : View) (lower upper : Bound) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.slice mutability view lower upper origin)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_len_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (view : View) :
    PreservesActivationChannels (evalProduce (fuel + 1) config environment channels (.len view)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_un_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (operation : Goose.Core.UnOp)
    (operand : Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.un operation operand origin)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_bin_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (operation : Goose.Core.BinOp)
    (left right : Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.bin operation left right origin)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_cmp_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (operation : Goose.Core.CmpOp)
    (left right : Expr) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.cmp operation left right)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_and_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (left right : Expr) :
    PreservesActivationChannels (evalProduce (fuel + 1) config environment channels (.and left right)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_or_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (left right : Expr) :
    PreservesActivationChannels (evalProduce (fuel + 1) config environment channels (.or left right)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_not_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (operand : Expr) :
    PreservesActivationChannels (evalProduce (fuel + 1) config environment channels (.not operand)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_conv_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (kind : Goose.Core.ConvKind)
    (target : Ty) (operand : Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.conv kind target operand origin)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_call_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (_previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (context : Goose.Core.ContextId)
    (arguments : List Arg) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.call context arguments origin)) := by
  simp only [evalProduce]; activation_channels_helper_eval _previousFresh previous config

private theorem evalProduce_push_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (owner : Place) (operand : Expr)
    (origin : Option Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.push owner operand origin)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_pop_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (owner : Place)
    (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (evalProduce (fuel + 1) config environment channels (.pop owner origin)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_ifE_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (condition : Expr)
    (thenBlock elseBlock : Block) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.ifE condition thenBlock elseBlock origin)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_arrLit_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.arrLit ty operands origin)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_fill_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (ty : Ty) (operand : Expr)
    (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.fill ty operand origin)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_structLit_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (ty : Ty) (operands : List Expr) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.structLit ty operands)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_bytes_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (ty : Ty) (bytes : List UInt8)
    (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.bytes ty bytes origin)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_str_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (ty : Ty) (arguments : List PrintArg)
    (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.str ty arguments origin)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_copy_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (ty : Ty) (source : Place)
    (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.copy ty source origin)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_resultLocal_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (varId : Goose.Core.VarId)
    (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.resultLocal varId origin)) := by
  simp only [evalProduce]; activation_channels_helper_eval previousFresh previous config

private theorem evalProduce_values_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (_previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (channels : List Channel) (operands : List Expr) :
    PreservesActivationChannels
      (evalProduce (fuel + 1) config environment channels (.values operands)) := by
  simp only [evalProduce]; activation_channels_helper_eval _previousFresh previous config

theorem evalProduce_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (expression : Expr) :
    PreservesActivationChannels (evalProduce (fuel + 1) config environment channels expression) := by
  cases expression with
  | lit ty value => exact evalProduce_lit_activationChannels_case fuel config previousFresh previous environment channels ty value
  | bool value => exact evalProduce_bool_activationChannels_case fuel config previousFresh previous environment channels value
  | read place => exact evalProduce_read_activationChannels_case fuel config previousFresh previous environment channels place
  | ref mutability place =>
      exact evalProduce_ref_activationChannels_case fuel config previousFresh previous environment channels mutability place
  | slice mutability view lower upper origin =>
      exact evalProduce_slice_activationChannels_case fuel config previousFresh previous environment channels mutability view lower upper origin
  | len view => exact evalProduce_len_activationChannels_case fuel config previousFresh previous environment channels view
  | un operation operand origin =>
      exact evalProduce_un_activationChannels_case fuel config previousFresh previous environment channels operation operand origin
  | bin operation left right origin =>
      exact evalProduce_bin_activationChannels_case fuel config previousFresh previous environment channels operation left right origin
  | cmp operation left right =>
      exact evalProduce_cmp_activationChannels_case fuel config previousFresh previous environment channels operation left right
  | «and» left right =>
      exact evalProduce_and_activationChannels_case fuel config previousFresh previous environment channels left right
  | «or» left right =>
      exact evalProduce_or_activationChannels_case fuel config previousFresh previous environment channels left right
  | «not» operand => exact evalProduce_not_activationChannels_case fuel config previousFresh previous environment channels operand
  | conv kind target operand origin =>
      exact evalProduce_conv_activationChannels_case fuel config previousFresh previous environment channels kind target operand origin
  | call context arguments origin =>
      exact evalProduce_call_activationChannels_case fuel config previousFresh previous environment channels context arguments origin
  | push owner operand origin =>
      exact evalProduce_push_activationChannels_case fuel config previousFresh previous environment channels owner operand origin
  | pop owner origin =>
      exact evalProduce_pop_activationChannels_case fuel config previousFresh previous environment channels owner origin
  | ifE condition thenBlock elseBlock origin =>
      exact evalProduce_ifE_activationChannels_case fuel config previousFresh previous environment channels condition thenBlock elseBlock origin
  | blockE block origin =>
      exact evalProduce_blockE_activationChannels_succ fuel config previousFresh previous environment channels block origin
  | arrLit ty operands origin =>
      exact evalProduce_arrLit_activationChannels_case fuel config previousFresh previous environment channels ty operands origin
  | fill ty operand origin =>
      exact evalProduce_fill_activationChannels_case fuel config previousFresh previous environment channels ty operand origin
  | structLit ty operands =>
      exact evalProduce_structLit_activationChannels_case fuel config previousFresh previous environment channels ty operands
  | bytes ty bytes origin =>
      exact evalProduce_bytes_activationChannels_case fuel config previousFresh previous environment channels ty bytes origin
  | str ty arguments origin =>
      exact evalProduce_str_activationChannels_case fuel config previousFresh previous environment channels ty arguments origin
  | copy ty source origin =>
      exact evalProduce_copy_activationChannels_case fuel config previousFresh previous environment channels ty source origin
  | resultLocal varId origin =>
      exact evalProduce_resultLocal_activationChannels_case fuel config previousFresh previous environment channels varId origin
  | values operands =>
      exact evalProduce_values_activationChannels_case fuel config previousFresh previous environment channels operands

end Goose.Proofs.ExitExecution

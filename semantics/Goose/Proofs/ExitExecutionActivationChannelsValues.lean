import Goose.Proofs.ExitExecutionActivationChannelsHelpers

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem evalBound_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (count : Nat) (defaultValue : Int) (operand : Bound) :
    PreservesActivationChannels (evalBound (fuel + 1) config environment count defaultValue operand) := by
  cases operand <;> simp only [evalBound] <;> activation_channels_helper_eval previousFresh previous config

private theorem evalValue_str_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (ty : Ty) (arguments : List PrintArg) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (evalValue (fuel + 1) config environment (.str ty arguments origin)) := by
  simp only [evalValue]
  apply preservesActivationChannels_bind
    (constructLocal ⟨config.module, environment.vars⟩ environment.act ty origin
      (.str ty arguments origin)
      (fun destination => buildExpr fuel config environment destination (.str ty arguments origin))) _
  · exact preservesActivationChannels_constructLocal _ _ _ _ _ _
      (fun destination => previous.build environment destination (.str ty arguments origin))
      (fun destination => previousFresh.build environment destination (.str ty arguments origin))
  · exact preservesFresh_constructLocal _ _ _ _ _ _
      (fun destination => previousFresh.build environment destination (.str ty arguments origin))
  · intro carrier
    apply preservesActivationChannels_bind (carrierValue carrier) _
    · exact preservesActivationChannels_of_stateQuery _ (stateQuery_carrierValue carrier)
    · exact stateQuery_preservesFresh _ (stateQuery_carrierValue carrier)
    · intro value
      by_cases nonfixed : ty.nonfixed
      · simpa [nonfixed] using preservesActivationChannels_pure value
      · simp only [nonfixed, Bool.false_eq_true, ↓reduceIte]
        cases value with
        | stored stored =>
            apply preservesActivationChannels_bind (getStorage stored.storage) _
            · exact preservesActivationChannels_of_stateQuery _ (stateQuery_getStorage _)
            · exact stateQuery_preservesFresh _ (stateQuery_getStorage _)
            · intro storage
              exact preservesActivationChannels_liftExcept
                (fixedValue fuel config.layout ty storage.bytes stored.start)
        | int _ _ | bool _ | unit | fixed _ | record _ _ | ref _ | slice _ _ _ =>
            exact preservesActivationChannels_fault .shape

private theorem evalValue_copy_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (ty : Ty) (source : Place) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (evalValue (fuel + 1) config environment (.copy ty source origin)) := by
  cases nonfixed : ty.nonfixed with
  | true =>
      simp only [evalValue, nonfixed]
      apply preservesActivationChannels_bind
        (constructLocal ⟨config.module, environment.vars⟩ environment.act ty origin
          (.copy ty source origin)
          (fun destination => buildExpr fuel config environment destination (.copy ty source origin))) _
      · exact preservesActivationChannels_constructLocal _ _ _ _ _ _
          (fun destination => previous.build environment destination (.copy ty source origin))
          (fun destination => previousFresh.build environment destination (.copy ty source origin))
      · exact preservesFresh_constructLocal _ _ _ _ _ _
          (fun destination => previousFresh.build environment destination (.copy ty source origin))
      · intro carrier
        exact preservesActivationChannels_of_stateQuery _ (stateQuery_carrierValue carrier)
  | false =>
      simp only [evalValue, nonfixed]
      apply preservesActivationChannels_bind (evalPlace fuel config environment source) _
      · exact previous.place environment source
      · exact previousFresh.place environment source
      · intro location
        apply preservesActivationChannels_bind (readLoc fuel config.layout location) _
        · exact preservesActivationChannels_of_stateQuery _ (stateQuery_readLoc fuel config.layout location)
        · exact stateQuery_preservesFresh _ (stateQuery_readLoc fuel config.layout location)
        · intro value
          cases ty with
          | arr element count =>
              cases value with
              | stored stored =>
                  apply preservesActivationChannels_bind (sampledStored stored) _
                  · exact preservesActivationChannels_of_stateQuery _ (stateQuery_sampledStored stored)
                  · exact stateQuery_preservesFresh _ (stateQuery_sampledStored stored)
                  · intro sampled
                    rcases sampled with ⟨bytes, run⟩
                    split
                    · exact preservesActivationChannels_fault .shape
                    · change PreservesActivationChannels
                        ((List.range count).mapM (readStoredElement fuel config.layout stored) >>= fun values =>
                          pure (Value.fixed values.toArray))
                      apply preservesActivationChannels_bind
                      · apply preservesActivationChannels_listMapM
                        · intro index
                          exact preservesActivationChannels_of_stateQuery _
                            (stateQuery_readStoredElement fuel config.layout stored index)
                        · intro index
                          exact stateQuery_preservesFresh _
                            (stateQuery_readStoredElement fuel config.layout stored index)
                      · exact preservesFresh_listMapM _ _ (by
                          intro index
                          exact stateQuery_preservesFresh _
                            (stateQuery_readStoredElement fuel config.layout stored index))
                      · intro values; exact preservesActivationChannels_pure _
              | int _ _ | bool _ | unit | fixed _ | record _ _ | ref _ | slice _ _ _ =>
                  exact preservesActivationChannels_pure _
          | bool | int _ | unit | varr _ | grow _ | growshrink _ | limited _ _
          | ref _ _ | slice _ _ | tuple _ | structT _ _ =>
              exact preservesActivationChannels_pure _

private theorem evalValue_lit_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Goose.Core.IntTy) (value : Int) :
    PreservesActivationChannels (evalValue (fuel + 1) config environment (.lit ty value)) := by
  simp only [evalValue]; exact preservesActivationChannels_pure _

private theorem evalValue_bool_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (value : Bool) :
    PreservesActivationChannels (evalValue (fuel + 1) config environment (.bool value)) := by
  simp only [evalValue]; exact preservesActivationChannels_pure _

private theorem evalValue_read_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (place : Place) :
    PreservesActivationChannels (evalValue (fuel + 1) config environment (.read place)) := by
  simp only [evalValue]; activation_channels_helper_eval previousFresh previous config

private theorem evalValue_ref_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (mutability : Goose.Core.Mutability) (place : Place) :
    PreservesActivationChannels (evalValue (fuel + 1) config environment (.ref mutability place)) := by
  simp only [evalValue]; activation_channels_helper_eval previousFresh previous config

private theorem evalValue_slice_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (mutability : Goose.Core.Mutability) (view : View)
    (lower upper : Bound) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalValue (fuel + 1) config environment (.slice mutability view lower upper origin)) := by
  simp only [evalValue]; activation_channels_helper_eval previousFresh previous config

private theorem evalValue_len_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (view : View) :
    PreservesActivationChannels (evalValue (fuel + 1) config environment (.len view)) := by
  simp only [evalValue]; activation_channels_helper_eval previousFresh previous config

private theorem evalValue_un_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (operation : Goose.Core.UnOp) (expression : Expr)
    (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalValue (fuel + 1) config environment (.un operation expression origin)) := by
  simp only [evalValue]; activation_channels_helper_eval previousFresh previous config

private theorem evalValue_bin_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (operation : Goose.Core.BinOp) (left right : Expr)
    (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalValue (fuel + 1) config environment (.bin operation left right origin)) := by
  simp only [evalValue]; activation_channels_helper_eval previousFresh previous config

private theorem evalValue_cmp_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (operation : Goose.Core.CmpOp) (left right : Expr) :
    PreservesActivationChannels
      (evalValue (fuel + 1) config environment (.cmp operation left right)) := by
  simp only [evalValue]; activation_channels_helper_eval previousFresh previous config

private theorem evalValue_and_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (left right : Expr) :
    PreservesActivationChannels (evalValue (fuel + 1) config environment (.and left right)) := by
  simp only [evalValue]; activation_channels_helper_eval previousFresh previous config

private theorem evalValue_or_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (left right : Expr) :
    PreservesActivationChannels (evalValue (fuel + 1) config environment (.or left right)) := by
  simp only [evalValue]; activation_channels_helper_eval previousFresh previous config

private theorem evalValue_not_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (expression : Expr) :
    PreservesActivationChannels (evalValue (fuel + 1) config environment (.not expression)) := by
  simp only [evalValue]; activation_channels_helper_eval previousFresh previous config

private theorem evalValue_conv_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (kind : Goose.Core.ConvKind) (target : Ty) (expression : Expr)
    (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalValue (fuel + 1) config environment (.conv kind target expression origin)) := by
  simp only [evalValue]; activation_channels_helper_eval previousFresh previous config

private theorem evalValue_call_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (context : Goose.Core.ContextId) (arguments : List Arg)
    (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalValue (fuel + 1) config environment (.call context arguments origin)) := by
  simp only [evalValue]; activation_channels_helper_eval previousFresh previous config

private theorem evalValue_push_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (_previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (owner : Place) (expression : Expr)
    (origin : Option Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalValue (fuel + 1) config environment (.push owner expression origin)) := by
  simp only [evalValue]; activation_channels_helper_eval _previousFresh previous config

private theorem evalValue_pop_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (owner : Place) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (evalValue (fuel + 1) config environment (.pop owner origin)) := by
  simp only [evalValue]; activation_channels_helper_eval previousFresh previous config

private theorem evalValue_ifE_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (condition : Expr) (thenBlock elseBlock : Block)
    (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalValue (fuel + 1) config environment (.ifE condition thenBlock elseBlock origin)) := by
  simp only [evalValue]; activation_channels_helper_eval previousFresh previous config

private theorem evalValue_blockE_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (block : Block) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalValue (fuel + 1) config environment (.blockE block origin)) := by
  simp only [evalValue]; activation_channels_helper_eval previousFresh previous config

private theorem evalValue_arrLit_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalValue (fuel + 1) config environment (.arrLit ty operands origin)) := by
  simp only [evalValue]; activation_channels_helper_eval previousFresh previous config

private theorem evalValue_fill_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (ty : Ty) (operand : Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalValue (fuel + 1) config environment (.fill ty operand origin)) := by
  cases ty <;> try simp only [evalValue] <;> activation_channels_helper_eval previousFresh previous config

private theorem evalValue_structLit_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr) :
    PreservesActivationChannels (evalValue (fuel + 1) config environment (.structLit ty operands)) := by
  cases ty <;> try simp only [evalValue] <;> activation_channels_helper_eval previousFresh previous config

private theorem evalValue_bytes_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalValue (fuel + 1) config environment (.bytes ty bytes origin)) := by
  cases ty with
  | slice mutability element =>
      cases element with
      | int integerType =>
          cases integerType <;> simp only [evalValue] <;>
            activation_channels_helper_eval previousFresh previous config
      | _ => simp only [evalValue] <;> activation_channels_helper_eval previousFresh previous config
  | _ => simp only [evalValue] <;> activation_channels_helper_eval previousFresh previous config

private theorem evalValue_values_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (_previousFresh : EvaluationPreservesFresh fuel config) (previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (operands : List Expr) :
    PreservesActivationChannels (evalValue (fuel + 1) config environment (.values operands)) := by
  cases operands with
  | nil => simp only [evalValue]; activation_channels_helper_eval _previousFresh previous config
  | cons operand rest =>
      cases rest with
      | nil => simp only [evalValue]; activation_channels_helper_eval _previousFresh previous config
      | cons _ _ => simp only [evalValue]; activation_channels_helper_eval _previousFresh previous config

private theorem evalValue_resultLocal_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (_previousFresh : EvaluationPreservesFresh fuel config) (_previous : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (varId : Goose.Core.VarId) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels
      (evalValue (fuel + 1) config environment (.resultLocal varId origin)) := by
  simp only [evalValue]; activation_channels_helper_eval _previousFresh _previous config

theorem evalValue_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (expression : Expr) :
    PreservesActivationChannels (evalValue (fuel + 1) config environment expression) := by
  cases expression with
  | lit ty value => exact evalValue_lit_activationChannels_case fuel config environment ty value
  | bool value => exact evalValue_bool_activationChannels_case fuel config environment value
  | read place => exact evalValue_read_activationChannels_case fuel config previousFresh previous environment place
  | ref mutability place => exact evalValue_ref_activationChannels_case fuel config previousFresh previous environment mutability place
  | slice mutability view lower upper origin =>
      exact evalValue_slice_activationChannels_case fuel config previousFresh previous environment mutability view lower upper origin
  | len view => exact evalValue_len_activationChannels_case fuel config previousFresh previous environment view
  | un operation expression origin =>
      exact evalValue_un_activationChannels_case fuel config previousFresh previous environment operation expression origin
  | bin operation left right origin =>
      exact evalValue_bin_activationChannels_case fuel config previousFresh previous environment operation left right origin
  | cmp operation left right =>
      exact evalValue_cmp_activationChannels_case fuel config previousFresh previous environment operation left right
  | «and» left right => exact evalValue_and_activationChannels_case fuel config previousFresh previous environment left right
  | «or» left right => exact evalValue_or_activationChannels_case fuel config previousFresh previous environment left right
  | «not» expression => exact evalValue_not_activationChannels_case fuel config previousFresh previous environment expression
  | conv kind target expression origin =>
      exact evalValue_conv_activationChannels_case fuel config previousFresh previous environment kind target expression origin
  | call context arguments origin =>
      exact evalValue_call_activationChannels_case fuel config previousFresh previous environment context arguments origin
  | push owner expression origin =>
      exact evalValue_push_activationChannels_case fuel config previousFresh previous environment owner expression origin
  | pop owner origin => exact evalValue_pop_activationChannels_case fuel config previousFresh previous environment owner origin
  | ifE condition thenBlock elseBlock origin =>
      exact evalValue_ifE_activationChannels_case fuel config previousFresh previous environment condition thenBlock elseBlock origin
  | blockE block origin => exact evalValue_blockE_activationChannels_case fuel config previousFresh previous environment block origin
  | arrLit ty operands origin =>
      exact evalValue_arrLit_activationChannels_case fuel config previousFresh previous environment ty operands origin
  | fill ty operand origin =>
      exact evalValue_fill_activationChannels_case fuel config previousFresh previous environment ty operand origin
  | structLit ty operands =>
      exact evalValue_structLit_activationChannels_case fuel config previousFresh previous environment ty operands
  | bytes ty bytes origin =>
      exact evalValue_bytes_activationChannels_case fuel config previousFresh previous environment ty bytes origin
  | str ty arguments origin =>
      exact evalValue_str_activationChannels_succ fuel config previousFresh previous environment ty arguments origin
  | copy ty source origin =>
      exact evalValue_copy_activationChannels_succ fuel config previousFresh previous environment ty source origin
  | resultLocal varId origin =>
      exact evalValue_resultLocal_activationChannels_case fuel config previousFresh previous environment varId origin
  | values operands => exact evalValue_values_activationChannels_case fuel config previousFresh previous environment operands

theorem evalPlace_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (operand : Place) : PreservesActivationChannels (evalPlace (fuel + 1) config environment operand) := by
  cases operand <;> simp only [evalPlace] <;> activation_channels_helper_eval previousFresh previous config

theorem evalView_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (operand : View) : PreservesActivationChannels (evalView (fuel + 1) config environment operand) := by
  cases operand <;> simp only [evalView] <;> first
    | exact preservesActivationChannels_bindRoot _ _
    | activation_channels_helper_eval previousFresh previous config

theorem evalOperands_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (operands : List Expr) :
    PreservesActivationChannels (evalOperands (fuel + 1) config environment channels operands) := by
  cases channels <;> cases operands <;> simp only [evalOperands] <;> activation_channels_helper_eval previousFresh previous config

theorem evalPrintArg_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (argument : PrintArg) : PreservesActivationChannels (evalPrintArg (fuel + 1) config environment argument) := by
  cases argument <;> simp only [evalPrintArg] <;> activation_channels_helper_eval previousFresh previous config

end Goose.Proofs.ExitExecution

import Goose.Proofs.ConstructionExecutionProtocolEvaluationContext

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

variable {predicate : ConstructionState → Prop} [primitives : ConstructionProtocolPrimitives predicate]
  [reservations : ConstructionReservationPrimitives predicate]
include primitives reservations

theorem evalValue_lit_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (_previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (ty : Goose.Core.IntTy) (value : Int) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.lit ty value)) := by
  simp only [evalValue]
  protocol_eval _previous

theorem evalValue_bool_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (_previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (value : Bool) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.bool value)) := by
  simp only [evalValue]
  protocol_eval _previous

theorem evalValue_read_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (place : Place) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.read place)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_ref_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (mutability : Goose.Core.Mutability) (place : Place) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.ref mutability place)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_slice_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (mutability : Goose.Core.Mutability) (view : View) (lo hi : Bound) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.slice mutability view lo hi origin)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_len_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (view : View) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.len view)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_un_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.UnOp) (expression : Expr) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.un operation expression origin)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_bin_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.BinOp) (first second : Expr) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.bin operation first second origin)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_cmp_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.CmpOp) (first second : Expr) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.cmp operation first second)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_and_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (first second : Expr) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.and first second)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_or_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (first second : Expr) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.or first second)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_not_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (expression : Expr) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.not expression)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_conv_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (kind : Goose.Core.ConvKind) (target : Ty) (expression : Expr) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.conv kind target expression origin)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_call_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.call context arguments origin)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_push_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Option Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.push owner expression origin)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_pop_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (owner : Place) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.pop owner origin)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_ifE_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (condition : Expr) (yes no : Block) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.ifE condition yes no origin)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_blockE_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (body : Block) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.blockE body origin)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_arrLit_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (ty : Ty) (operands : List Expr) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.arrLit ty operands origin)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_fill_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (ty : Ty) (expression : Expr) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.fill ty expression origin)) := by
  cases ty <;> simp only [evalValue]
  all_goals protocol_eval previous

theorem evalValue_structLit_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (ty : Ty) (operands : List Expr) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.structLit ty operands)) := by
  cases ty <;> simp only [evalValue]
  all_goals protocol_eval previous

theorem evalValue_bytes_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.bytes ty bytes origin)) := by
  cases ty <;> try simp only [evalValue]
  all_goals protocol_eval previous
  case slice mutability element =>
    cases element <;> try simp only [evalValue]
    all_goals protocol_eval previous
    case int ty =>
      cases ty <;> simp only [evalValue]
      all_goals protocol_eval previous

theorem evalValue_str_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (ty : Ty) (arguments : List PrintArg) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.str ty arguments origin)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_copy_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (ty : Ty) (source : Place) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.copy ty source origin)) := by
  simp only [evalValue]
  protocol_eval previous

theorem evalValue_resultLocal_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (_previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.resultLocal localVar origin)) := by
  simp only [evalValue]
  protocol_eval _previous

theorem evalValue_values_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (operands : List Expr) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.values operands)) := by
  cases operands with
  | nil => simpa only [evalValue] using preservesConstructionInvariant_pure Value.unit
  | cons expression operands =>
      cases operands <;> simp only [evalValue]
      all_goals protocol_eval previous

theorem evalValue_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation) (expression : Expr) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment expression) := by
  cases expression with
  | lit ty value => exact evalValue_lit_preservesConstructionInvariant_succ fuel config previous environment ty value
  | bool value => exact evalValue_bool_preservesConstructionInvariant_succ fuel config previous environment value
  | read place => exact evalValue_read_preservesConstructionInvariant_succ fuel config previous environment place
  | ref mutability place => exact evalValue_ref_preservesConstructionInvariant_succ fuel config previous environment mutability place
  | slice mutability view lo hi origin => exact evalValue_slice_preservesConstructionInvariant_succ fuel config previous environment mutability view lo hi origin
  | len view => exact evalValue_len_preservesConstructionInvariant_succ fuel config previous environment view
  | un operation expression origin => exact evalValue_un_preservesConstructionInvariant_succ fuel config previous environment operation expression origin
  | bin operation first second origin => exact evalValue_bin_preservesConstructionInvariant_succ fuel config previous environment operation first second origin
  | cmp operation first second => exact evalValue_cmp_preservesConstructionInvariant_succ fuel config previous environment operation first second
  | and first second => exact evalValue_and_preservesConstructionInvariant_succ fuel config previous environment first second
  | or first second => exact evalValue_or_preservesConstructionInvariant_succ fuel config previous environment first second
  | not expression => exact evalValue_not_preservesConstructionInvariant_succ fuel config previous environment expression
  | conv kind target expression origin => exact evalValue_conv_preservesConstructionInvariant_succ fuel config previous environment kind target expression origin
  | call context arguments origin => exact evalValue_call_preservesConstructionInvariant_succ fuel config previous environment context arguments origin
  | push owner expression origin => exact evalValue_push_preservesConstructionInvariant_succ fuel config previous environment owner expression origin
  | pop owner origin => exact evalValue_pop_preservesConstructionInvariant_succ fuel config previous environment owner origin
  | ifE condition yes no origin => exact evalValue_ifE_preservesConstructionInvariant_succ fuel config previous environment condition yes no origin
  | blockE body origin => exact evalValue_blockE_preservesConstructionInvariant_succ fuel config previous environment body origin
  | arrLit ty operands origin => exact evalValue_arrLit_preservesConstructionInvariant_succ fuel config previous environment ty operands origin
  | fill ty expression origin => exact evalValue_fill_preservesConstructionInvariant_succ fuel config previous environment ty expression origin
  | structLit ty operands => exact evalValue_structLit_preservesConstructionInvariant_succ fuel config previous environment ty operands
  | bytes ty bytes origin => exact evalValue_bytes_preservesConstructionInvariant_succ fuel config previous environment ty bytes origin
  | str ty arguments origin => exact evalValue_str_preservesConstructionInvariant_succ fuel config previous environment ty arguments origin
  | copy ty source origin => exact evalValue_copy_preservesConstructionInvariant_succ fuel config previous environment ty source origin
  | resultLocal localVar origin => exact evalValue_resultLocal_preservesConstructionInvariant_succ fuel config previous environment localVar origin
  | values operands => exact evalValue_values_preservesConstructionInvariant_succ fuel config previous environment operands


end Goose.Proofs.ConstructionExecutionProtocol

import Goose.Lower.Validation.PermissionPreservationExpressionPure
import Goose.Lower.Validation.PermissionInstructionStorageSourceBase
import Goose.Lower.Validation.ExpressionTypingScalarOps
import Goose.Lower.Validation.ScalarTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem permission_source_literal (env : Core.TEnv) (func : Func) (results : List Ty) (type : IntTy) (value : Int) :
    PermissionStorageExprChild env func results (.lit type value) := by
  intro result start finish source before after id generated run
  exact newPermissions_free_emitDef (by trivial) run

theorem permission_source_bool (env : Core.TEnv) (func : Func) (results : List Ty) (value : Bool) :
    PermissionStorageExprChild env func results (.bool value) := by
  intro result start finish source before after id generated run
  exact newPermissions_free_emitDef (by trivial) run

theorem permission_source_not {env : Core.TEnv} {func : Func} {results : List Ty}
    (expr : Expr) (child : PermissionStorageExprChild env func results expr) :
    PermissionStorageExprChild env func results (.not expr) := by
  intro result start finish source before after value generated run
  obtain ⟨childFinish, childSource, _⟩ := tyExpr_not_child source
  obtain ⟨childValue, middle, childRun, remaining⟩ := bind_eq.mp run
  exact newPermissions_lowerExpr_not childRun (child childSource generated childRun) generated run

theorem permission_source_unary {env : Core.TEnv} {func : Func} {results : List Ty}
    (op : UnOp) (expr : Expr) (origin : OriginId) (child : PermissionStorageExprChild env func results expr) :
    PermissionStorageExprChild env func results (.un op expr origin) := by
  intro result start finish source before after value generated run
  obtain ⟨childStart, childFinish, type, childSource, _, signed⟩ := tyExpr_un_child source
  obtain ⟨childValue, middle, childRun, remaining⟩ := bind_eq.mp run
  exact newPermissions_lowerExpr_un childRun (child childSource generated childRun) generated run

theorem permission_source_conversion {env : Core.TEnv} {func : Func} {results : List Ty}
    (kind : ConvKind) (target : Ty) (expr : Expr) (origin : OriginId) (child : PermissionStorageExprChild env func results expr) :
    PermissionStorageExprChild env func results (.conv kind target expr origin) := by
  intro result start finish source before after value generated run
  obtain ⟨src, dst, childStart, childFinish, childSource, targetShape, _, widening⟩ := tyExpr_conversion_child source
  subst target
  obtain ⟨childValue, middle, childRun, remaining⟩ := bind_eq.mp run
  exact newPermissions_lowerExpr_conv childRun (child childSource generated childRun) generated run

theorem permission_source_binary {env : Core.TEnv} {func : Func} {results : List Ty}
    (op : BinOp) (left right : Expr) (origin : OriginId)
    (leftChild : PermissionStorageExprChild env func results left)
    (rightChild : PermissionStorageExprChild env func results right) :
    PermissionStorageExprChild env func results (.bin op left right origin) := by
  intro result start finish source before after value generated run
  obtain ⟨leftStart, leftFinish, rightStart, rightFinish, type, leftSource, rightSource, _⟩ := tyExpr_bin_children source
  obtain ⟨leftValue, leftState, leftRun, remaining⟩ := bind_eq.mp run
  obtain ⟨rightValue, middle, rightRun, remaining⟩ := bind_eq.mp remaining
  exact newPermissions_lowerExpr_bin leftRun rightRun
    (leftChild leftSource generated leftRun)
    ((rightChild rightSource (generated.lowerExpr left leftRun) rightRun).weaken
      (advB_lowerExpr left _ _ _ _ leftRun).vals) generated run

theorem permission_source_comparison {env : Core.TEnv} {func : Func} {results : List Ty}
    (op : CmpOp) (left right : Expr)
    (leftChild : PermissionStorageExprChild env func results left)
    (rightChild : PermissionStorageExprChild env func results right) :
    PermissionStorageExprChild env func results (.cmp op left right) := by
  intro result start finish source before after value generated run
  obtain ⟨leftType, rightType, leftFinish, rightFinish, leftSource, rightSource, _⟩ := tyExpr_comparison_children source
  obtain ⟨leftValue, leftState, leftRun, remaining⟩ := bind_eq.mp run
  obtain ⟨rightValue, middle, rightRun, remaining⟩ := bind_eq.mp remaining
  exact newPermissions_lowerExpr_cmp leftRun rightRun
    (leftChild leftSource generated leftRun)
    ((rightChild rightSource (generated.lowerExpr left leftRun) rightRun).weaken
      (advB_lowerExpr left _ _ _ _ leftRun).vals) generated run

#print axioms permission_source_literal
#print axioms permission_source_bool
#print axioms permission_source_not
#print axioms permission_source_unary
#print axioms permission_source_conversion
#print axioms permission_source_binary
#print axioms permission_source_comparison

end Goose.Lower.Validation

import Goose.Lower.Validation.StorageWalkSourceContracts
import Goose.Lower.Validation.ExpressionTypingScalarOps
import Goose.Lower.Validation.ScalarTyping
import Goose.Lower.Validation.DereferenceTyping
import Goose.Lower.Validation.ViewTyping
import Goose.Lower.Validation.ExpressionTypingSliceOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem storageWalk_source_literal (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) (type : IntTy) (value : Int) :
    StorageWalkSourceExpression env results stack (.lit type value) := by
  intro result start finish source visible loop
  exact StorageWalkAction.emitDef _ stack loop (.constInt type value) (by simp [StorageInstructionVisible])

theorem storageWalk_source_bool (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) (value : Bool) :
    StorageWalkSourceExpression env results stack (.bool value) := by
  intro result start finish source visible loop
  exact StorageWalkAction.emitDef _ stack loop (.constBool value) (by simp [StorageInstructionVisible])

theorem storageWalk_source_not {env : Core.TEnv} {results : List Ty} {stack : List ScopeId} (expr : Expr)
    (child : StorageWalkSourceExpression env results stack expr) : StorageWalkSourceExpression env results stack (.not expr) := by
  intro result start finish source visible loop
  obtain ⟨childFinish, childSource, _⟩ := tyExpr_not_child source
  exact ((child childSource visible loop).bind fun value =>
    StorageWalkAction.emitDef _ stack loop (.boolNot value) (by simp [StorageInstructionVisible]))

theorem storageWalk_source_unary {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (op : UnOp) (expr : Expr) (origin : OriginId) (child : StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceExpression env results stack (.un op expr origin) := by
  intro result start finish source visible loop
  obtain ⟨childStart, childFinish, type, childSource, _, signed⟩ := tyExpr_un_child source
  exact ((child childSource visible loop).bind fun value =>
    (StorageWalkAction.intTyOf _ stack loop value).bind fun type =>
      StorageWalkAction.emitDef _ stack loop (.un op type value (some origin)) (by simp [StorageInstructionVisible]))

theorem storageWalk_source_binary {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (op : BinOp) (left right : Expr) (origin : OriginId)
    (leftChild : StorageWalkSourceExpression env results stack left) (rightChild : StorageWalkSourceExpression env results stack right) :
    StorageWalkSourceExpression env results stack (.bin op left right origin) := by
  intro result start finish source visible loop
  obtain ⟨leftStart, leftFinish, rightStart, rightFinish, type, leftSource, rightSource, _⟩ := tyExpr_bin_children source
  exact ((leftChild leftSource visible loop).bind fun x =>
    (rightChild rightSource visible loop).bind fun y =>
      (StorageWalkAction.intTyOf _ stack loop x).bind fun type =>
        StorageWalkAction.emitDef _ stack loop (.bin op type x y (some origin)) (by simp [StorageInstructionVisible]))

theorem storageWalk_source_comparison {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (op : CmpOp) (left right : Expr)
    (leftChild : StorageWalkSourceExpression env results stack left) (rightChild : StorageWalkSourceExpression env results stack right) :
    StorageWalkSourceExpression env results stack (.cmp op left right) := by
  intro result start finish source visible loop
  obtain ⟨leftType, rightType, leftFinish, rightFinish, leftSource, rightSource, _⟩ := tyExpr_comparison_children source

  refine (leftChild leftSource visible loop).bind fun x =>
    (rightChild rightSource visible loop).bind fun y =>
      (StorageWalkAction.valTy _ stack loop x).bind fun type => ?_
  cases type with
  | data type => cases type <;> exact StorageWalkAction.emitDef _ stack loop _ (by simp [StorageInstructionVisible])
  | view _ _ => exact StorageWalkAction.emitDef _ stack loop _ (by simp [StorageInstructionVisible])

theorem storageWalk_source_conversion {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (kind : ConvKind) (target : Ty) (expr : Expr) (origin : OriginId)
    (child : StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceExpression env results stack (.conv kind target expr origin) := by
  intro result start finish source visible loop
  obtain ⟨src, dst, childStart, childFinish, childSource, targetShape, _, widening⟩ := tyExpr_conversion_child source
  subst target
  exact ((child childSource visible loop).bind fun value =>
    (StorageWalkAction.intTyOf _ stack loop value).bind fun type =>
      StorageWalkAction.emitDef _ stack loop (.conv kind type dst value (some origin)) (by simp [StorageInstructionVisible]))

#print axioms storageWalk_source_literal
#print axioms storageWalk_source_bool
#print axioms storageWalk_source_not
#print axioms storageWalk_source_unary
#print axioms storageWalk_source_binary
#print axioms storageWalk_source_comparison
#print axioms storageWalk_source_conversion

end Goose.Lower.Validation

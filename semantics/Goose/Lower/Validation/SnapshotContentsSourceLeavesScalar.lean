import Goose.Lower.Validation.SnapshotContentsSourceLeavesActions
import Goose.Lower.Validation.ExpressionTypingScalarOps
import Goose.Lower.Validation.ScalarTyping
import Goose.Lower.Validation.DereferenceTyping
import Goose.Lower.Validation.ViewTyping
import Goose.Lower.Validation.ExpressionTypingSliceOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem snapshot_source_literal (env : Core.TEnv) (results : List Ty) (type : IntTy) (value : Int) :
    SnapshotSourceExpression env results (.lit type value) := by
  intro result start finish source
  exact (SnapshotSourceAction.emitDef _ none (.constInt type value) (by intros; intro h; cases h)).snapshots

theorem snapshot_source_bool (env : Core.TEnv) (results : List Ty) (value : Bool) :
    SnapshotSourceExpression env results (.bool value) := by
  intro result start finish source
  exact (SnapshotSourceAction.emitDef _ none (.constBool value) (by intros; intro h; cases h)).snapshots

theorem snapshot_source_not {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : SnapshotSourceExpression env results expr) : SnapshotSourceExpression env results (.not expr) := by
  intro result start finish source
  obtain ⟨childFinish, childSource, _⟩ := tyExpr_not_child source
  exact ((SnapshotSourceAction.lowerExpr expr (child childSource)).bind fun value =>
    SnapshotSourceAction.emitDef _ none (.boolNot value) (by intros; intro h; cases h)).snapshots

theorem snapshot_source_unary {env : Core.TEnv} {results : List Ty}
    (op : UnOp) (expr : Expr) (origin : OriginId) (child : SnapshotSourceExpression env results expr) :
    SnapshotSourceExpression env results (.un op expr origin) := by
  intro result start finish source
  obtain ⟨childStart, childFinish, type, childSource, _, signed⟩ := tyExpr_un_child source
  exact ((SnapshotSourceAction.lowerExpr expr (child childSource)).bind fun value =>
    (SnapshotSourceAction.intTyOf _ none value).bind fun type =>
      SnapshotSourceAction.emitDef _ none (.un op type value (some origin)) (by intros; intro h; cases h)).snapshots

theorem snapshot_source_binary {env : Core.TEnv} {results : List Ty}
    (op : BinOp) (left right : Expr) (origin : OriginId)
    (leftChild : SnapshotSourceExpression env results left) (rightChild : SnapshotSourceExpression env results right) :
    SnapshotSourceExpression env results (.bin op left right origin) := by
  intro result start finish source
  obtain ⟨leftStart, leftFinish, rightStart, rightFinish, type, leftSource, rightSource, _⟩ := tyExpr_bin_children source
  exact ((SnapshotSourceAction.lowerExpr left (leftChild leftSource)).bind fun x =>
    (SnapshotSourceAction.lowerExpr right (rightChild rightSource)).bind fun y =>
      (SnapshotSourceAction.intTyOf _ none x).bind fun type =>
        SnapshotSourceAction.emitDef _ none (.bin op type x y (some origin)) (by intros; intro h; cases h)).snapshots

theorem snapshot_source_comparison {env : Core.TEnv} {results : List Ty}
    (op : CmpOp) (left right : Expr)
    (leftChild : SnapshotSourceExpression env results left) (rightChild : SnapshotSourceExpression env results right) :
    SnapshotSourceExpression env results (.cmp op left right) := by
  intro result start finish source
  obtain ⟨leftType, rightType, leftFinish, rightFinish, leftSource, rightSource, _⟩ := tyExpr_comparison_children source
  apply SnapshotSourceAction.snapshots
  refine (SnapshotSourceAction.lowerExpr left (leftChild leftSource)).bind fun x =>
    (SnapshotSourceAction.lowerExpr right (rightChild rightSource)).bind fun y =>
      (SnapshotSourceAction.valTy _ none x).bind fun type => ?_
  cases type with
  | data type => cases type <;> exact SnapshotSourceAction.emitDef _ none _ (by intros; intro h; cases h)
  | view _ _ => exact SnapshotSourceAction.emitDef _ none _ (by intros; intro h; cases h)

theorem snapshot_source_conversion {env : Core.TEnv} {results : List Ty}
    (kind : ConvKind) (target : Ty) (expr : Expr) (origin : OriginId)
    (child : SnapshotSourceExpression env results expr) :
    SnapshotSourceExpression env results (.conv kind target expr origin) := by
  intro result start finish source
  obtain ⟨src, dst, childStart, childFinish, childSource, targetShape, _, widening⟩ := tyExpr_conversion_child source
  subst target
  exact ((SnapshotSourceAction.lowerExpr expr (child childSource)).bind fun value =>
    (SnapshotSourceAction.intTyOf _ none value).bind fun type =>
      SnapshotSourceAction.emitDef _ none (.conv kind type dst value (some origin)) (by intros; intro h; cases h)).snapshots

end Goose.Lower.Validation

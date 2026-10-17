import Goose.Lower.Validation.EmittedMetadataActions
import Goose.Lower.Validation.ExpressionTypingScalarOps
import Goose.Lower.Validation.ScalarTyping
import Goose.Lower.Validation.DereferenceTyping
import Goose.Lower.Validation.ViewTyping
import Goose.Lower.Validation.ExpressionTypingSliceOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem metadata_source_literal (env : Core.TEnv) (results : List Ty) (type : IntTy) (value : Int) :
    EmittedMetadataSourceExpression env results (.lit type value) := by
  intro agreement result start finish source
  exact (EmittedMetadataAction.emitDef _ none (.constInt type value)).metadata

theorem metadata_source_bool (env : Core.TEnv) (results : List Ty) (value : Bool) :
    EmittedMetadataSourceExpression env results (.bool value) := by
  intro agreement result start finish source
  exact (EmittedMetadataAction.emitDef _ none (.constBool value)).metadata

theorem metadata_source_not {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : EmittedMetadataSourceExpression env results expr) : EmittedMetadataSourceExpression env results (.not expr) := by
  intro agreement result start finish source
  obtain ⟨childFinish, childSource, _⟩ := tyExpr_not_child source
  exact ((EmittedMetadataAction.lowerExpr expr (child agreement childSource)).bind fun value =>
    EmittedMetadataAction.emitDef _ none (.boolNot value)).metadata

theorem metadata_source_unary {env : Core.TEnv} {results : List Ty}
    (op : UnOp) (expr : Expr) (origin : OriginId) (child : EmittedMetadataSourceExpression env results expr) :
    EmittedMetadataSourceExpression env results (.un op expr origin) := by
  intro agreement result start finish source
  obtain ⟨childStart, childFinish, type, childSource, _, signed⟩ := tyExpr_un_child source
  exact ((EmittedMetadataAction.lowerExpr expr (child agreement childSource)).bind fun value =>
    (EmittedMetadataAction.intTyOf _ none value).bind fun type =>
      EmittedMetadataAction.emitDef _ none (.un op type value (some origin))).metadata

theorem metadata_source_binary {env : Core.TEnv} {results : List Ty}
    (op : BinOp) (left right : Expr) (origin : OriginId)
    (leftChild : EmittedMetadataSourceExpression env results left) (rightChild : EmittedMetadataSourceExpression env results right) :
    EmittedMetadataSourceExpression env results (.bin op left right origin) := by
  intro agreement result start finish source
  obtain ⟨leftStart, leftFinish, rightStart, rightFinish, type, leftSource, rightSource, _⟩ := tyExpr_bin_children source
  exact ((EmittedMetadataAction.lowerExpr left (leftChild agreement leftSource)).bind fun x =>
    (EmittedMetadataAction.lowerExpr right (rightChild agreement rightSource)).bind fun y =>
      (EmittedMetadataAction.intTyOf _ none x).bind fun type =>
        EmittedMetadataAction.emitDef _ none (.bin op type x y (some origin))).metadata

theorem metadata_source_comparison {env : Core.TEnv} {results : List Ty}
    (op : CmpOp) (left right : Expr)
    (leftChild : EmittedMetadataSourceExpression env results left) (rightChild : EmittedMetadataSourceExpression env results right) :
    EmittedMetadataSourceExpression env results (.cmp op left right) := by
  intro agreement result start finish source
  obtain ⟨leftType, rightType, leftFinish, rightFinish, leftSource, rightSource, _⟩ := tyExpr_comparison_children source
  apply EmittedMetadataAction.metadata
  refine (EmittedMetadataAction.lowerExpr left (leftChild agreement leftSource)).bind fun x =>
    (EmittedMetadataAction.lowerExpr right (rightChild agreement rightSource)).bind fun y =>
      (EmittedMetadataAction.valTy _ none x).bind fun type => ?_
  cases type with
  | data type => cases type <;> exact EmittedMetadataAction.emitDef _ none _
  | view _ _ => exact EmittedMetadataAction.emitDef _ none _

theorem metadata_source_conversion {env : Core.TEnv} {results : List Ty}
    (kind : ConvKind) (target : Ty) (expr : Expr) (origin : OriginId)
    (child : EmittedMetadataSourceExpression env results expr) :
    EmittedMetadataSourceExpression env results (.conv kind target expr origin) := by
  intro agreement result start finish source
  obtain ⟨src, dst, childStart, childFinish, childSource, targetShape, _, widening⟩ := tyExpr_conversion_child source
  subst target
  exact ((EmittedMetadataAction.lowerExpr expr (child agreement childSource)).bind fun value =>
    (EmittedMetadataAction.intTyOf _ none value).bind fun type =>
      EmittedMetadataAction.emitDef _ none (.conv kind type dst value (some origin))).metadata

end Goose.Lower.Validation

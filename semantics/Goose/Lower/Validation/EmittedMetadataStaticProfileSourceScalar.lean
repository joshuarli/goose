import Goose.Lower.Validation.EmittedMetadataStaticProfileSourceContracts
import Goose.Lower.Validation.ExpressionTypingScalarOps
import Goose.Lower.Validation.ScalarTyping
import Goose.Lower.Validation.DereferenceTyping
import Goose.Lower.Validation.ViewTyping
import Goose.Lower.Validation.ExpressionTypingSliceOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem profile_source_literal (env : Core.TEnv) (results : List Ty) (type : IntTy) (value : Int) :
    EmittedProfileSourceExpression env results (.lit type value) := by
  intro result start finish source
  exact (EmittedProfileRun.emitDef (.constInt type value) (by intro; trivial))

theorem profile_source_bool (env : Core.TEnv) (results : List Ty) (value : Bool) :
    EmittedProfileSourceExpression env results (.bool value) := by
  intro result start finish source
  exact (EmittedProfileRun.emitDef (.constBool value) (by intro; trivial))

theorem profile_source_not {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : EmittedProfileSourceExpression env results expr) : EmittedProfileSourceExpression env results (.not expr) := by
  intro result start finish source
  obtain ⟨childFinish, childSource, _⟩ := tyExpr_not_child source
  exact ((child childSource).bind fun value =>
    EmittedProfileRun.emitDef (.boolNot value) (by intro; trivial))

theorem profile_source_unary {env : Core.TEnv} {results : List Ty}
    (op : UnOp) (expr : Expr) (origin : OriginId) (child : EmittedProfileSourceExpression env results expr) :
    EmittedProfileSourceExpression env results (.un op expr origin) := by
  intro result start finish source
  obtain ⟨childStart, childFinish, type, childSource, _, signed⟩ := tyExpr_un_child source
  exact ((child childSource).bind fun value =>
    (EmittedProfileRun.intTyOf value).bind fun type =>
      EmittedProfileRun.emitDef (.un op type value (some origin)) (by intro; trivial))

theorem profile_source_binary {env : Core.TEnv} {results : List Ty}
    (op : BinOp) (left right : Expr) (origin : OriginId)
    (leftChild : EmittedProfileSourceExpression env results left) (rightChild : EmittedProfileSourceExpression env results right) :
    EmittedProfileSourceExpression env results (.bin op left right origin) := by
  intro result start finish source
  obtain ⟨leftStart, leftFinish, rightStart, rightFinish, type, leftSource, rightSource, _⟩ := tyExpr_bin_children source
  exact ((leftChild leftSource).bind fun x =>
    (rightChild rightSource).bind fun y =>
      (EmittedProfileRun.intTyOf x).bind fun type =>
        EmittedProfileRun.emitDef (.bin op type x y (some origin)) (by intro; trivial))

theorem profile_source_comparison {env : Core.TEnv} {results : List Ty}
    (op : CmpOp) (left right : Expr)
    (leftChild : EmittedProfileSourceExpression env results left) (rightChild : EmittedProfileSourceExpression env results right) :
    EmittedProfileSourceExpression env results (.cmp op left right) := by
  intro result start finish source
  obtain ⟨leftType, rightType, leftFinish, rightFinish, leftSource, rightSource, _⟩ := tyExpr_comparison_children source
  refine (leftChild leftSource).bind fun x =>
    (rightChild rightSource).bind fun y =>
      (EmittedProfileRun.valTy x).bind fun type => ?_
  cases type with
  | data type => cases type <;> exact EmittedProfileRun.emitDef _ (by intro; trivial)
  | view _ _ => exact EmittedProfileRun.emitDef _ (by intro; trivial)

theorem profile_source_conversion {env : Core.TEnv} {results : List Ty}
    (kind : ConvKind) (target : Ty) (expr : Expr) (origin : OriginId)
    (child : EmittedProfileSourceExpression env results expr) :
    EmittedProfileSourceExpression env results (.conv kind target expr origin) := by
  intro result start finish source
  obtain ⟨src, dst, childStart, childFinish, childSource, targetShape, _, widening⟩ := tyExpr_conversion_child source
  subst target
  exact ((child childSource).bind fun value =>
    (EmittedProfileRun.intTyOf value).bind fun type =>
      EmittedProfileRun.emitDef (.conv kind type dst value (some origin)) (by intro; trivial))

end Goose.Lower.Validation

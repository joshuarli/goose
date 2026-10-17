import Goose.Lower.Validation.CfgSourceEdgeContracts

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem cfg_source_literal (env : Core.TEnv) (results : List Ty) (ty : IntTy) (value : Int) :
    CfgSourceExpression env results (.lit ty value) := by
  intro output start finish source
  exact generated_edge_emitDef _ _ _

theorem cfg_source_boolean (env : Core.TEnv) (results : List Ty) (value : Bool) :
    CfgSourceExpression env results (.bool value) := by
  intro output start finish source
  exact generated_edge_emitDef _ _ _

theorem cfg_source_read {env : Core.TEnv} {results : List Ty} (place : Place)
    (child : CfgSourcePlace env results place) : CfgSourceExpression env results (.read place) := by
  intro output start finish source
  obtain ⟨info, next, placeSource, _⟩ := tyExpr_read_place source
  exact (child placeSource).bind fun address => (generated_edge_emitDef _ _ (.load address)).bind fun value =>
    (generated_edge_recordReadValueRootRecipe _ _ value place).bind fun _ => generated_edge_pure _ _ value

theorem cfg_source_reference {env : Core.TEnv} {results : List Ty} (mu : Mutability) (place : Place)
    (child : CfgSourcePlace env results place) : CfgSourceExpression env results (.ref mu place) := by
  intro output start finish source
  obtain ⟨info, next, placeSource, _, _⟩ := tyExpr_ref_place source
  exact (child placeSource).bind fun value => generated_edge_borrowTo _ _ mu value

theorem cfg_source_unary {env : Core.TEnv} {results : List Ty} (op : UnOp) (expr : Expr) (origin : OriginId)
    (child : CfgSourceExpression env results expr) : CfgSourceExpression env results (.un op expr origin) := by
  intro output start finish source
  obtain ⟨childStart, childFinish, ty, childSource, _, _⟩ := tyExpr_un_child source
  exact (child childSource).bind fun value => (generated_edge_intTyOf _ _ value).bind fun _ => generated_edge_emitDef _ _ _

theorem cfg_source_binary {env : Core.TEnv} {results : List Ty} (op : BinOp) (left right : Expr) (origin : OriginId)
    (leftChild : CfgSourceExpression env results left) (rightChild : CfgSourceExpression env results right) :
    CfgSourceExpression env results (.bin op left right origin) := by
  intro output start finish source
  obtain ⟨leftStart, leftFinish, rightStart, rightFinish, ty, leftSource, rightSource, _⟩ := tyExpr_bin_children source
  exact (leftChild leftSource).bind fun x => (rightChild rightSource).bind fun y =>
    (generated_edge_intTyOf _ _ x).bind fun _ => generated_edge_emitDef _ _ _

theorem cfg_source_not {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : CfgSourceExpression env results expr) : CfgSourceExpression env results (.not expr) := by
  intro output start finish source
  obtain ⟨childFinish, childSource, _⟩ := tyExpr_not_child source
  exact (child childSource).bind fun _ => generated_edge_emitDef _ _ _

theorem cfg_source_conversion {env : Core.TEnv} {results : List Ty} (kind : ConvKind) (ty : Ty)
    (expr : Expr) (origin : OriginId) (child : CfgSourceExpression env results expr) :
    CfgSourceExpression env results (.conv kind ty expr origin) := by
  intro output start finish source
  obtain ⟨src, dst, childStart, childFinish, childSource, _, _, _⟩ := tyExpr_conversion_child source
  exact (child childSource).bind fun value => (generated_edge_intTyOf _ _ value).bind fun _ => generated_edge_emitDef _ _ _

theorem cfg_source_comparison {env : Core.TEnv} {results : List Ty} (op : CmpOp) (left right : Expr)
    (leftChild : CfgSourceExpression env results left) (rightChild : CfgSourceExpression env results right) :
    CfgSourceExpression env results (.cmp op left right) := by
  intro output start finish source
  obtain ⟨leftTy, rightTy, leftFinish, rightFinish, leftSource, rightSource, _, _⟩ := tyExpr_comparison_children source
  refine (leftChild leftSource).bind fun x => (rightChild rightSource).bind fun y =>
    (generated_edge_valTy _ _ x).bind fun ty => ?_
  cases ty with
  | data ty => cases ty <;> exact generated_edge_emitDef _ _ _
  | view _ _ => exact generated_edge_emitDef _ _ _

theorem cfg_source_pop {env : Core.TEnv} {results : List Ty} (owner : Place) (origin : OriginId)
    (child : CfgSourcePlace env results owner) : CfgSourceExpression env results (.pop owner origin) := by
  intro output start finish source
  obtain ⟨info, ownerStart, ownerFinish, ownerSource, _⟩ := tyExpr_pop_owner source
  exact (child ownerSource).bind fun _ => generated_edge_emitDef _ _ _

theorem cfg_source_push {env : Core.TEnv} {results : List Ty} (owner : Place) (expr : Expr)
    (origin : Option OriginId) (ownerChild : CfgSourcePlace env results owner)
    (valueChild : CfgSourceExpression env results expr) : CfgSourceExpression env results (.push owner expr origin) := by
  intro output start finish source
  obtain ⟨info, element, ownerStart, ownerFinish, valueStart, valueFinish, ownerSource, _, valueSource, _⟩ := tyExpr_push_children source
  exact (ownerChild ownerSource).bind fun _ => (valueChild valueSource).bind fun _ => generated_edge_emitDef _ _ _

end Goose.Lower.Validation

import Goose.Lower.Validation.CfgSourceEdgeContracts
import Goose.Lower.Validation.SourceStatementTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem cfg_source_let {env : Core.TEnv} {results : List Ty} (x : VarId) (expr : Expr) (origin : OriginId)
    (child : CfgSourceExpression env results expr) : CfgSourceStatement env results (.letS x expr origin) := by
  intro output scope start finish source context
  obtain ⟨localVar, childTy, childStart, _, childSource, _, _⟩ := tyStmt_let_children source
  exact ((child childSource).withLoop context).bind fun value =>
    (generated_edge_coerceSlot _ _ x value origin).bind fun _ => generated_edge_emitEffect _ _ _

theorem cfg_source_assign {env : Core.TEnv} {results : List Ty} (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : CfgSourcePlace env results place) (valueChild : CfgSourceExpression env results expr) :
    CfgSourceStatement env results (.assign place expr origin) := by
  intro output scope start finish source context
  obtain ⟨info, childStart, placeSource, valueSource, _⟩ := tyStmt_assign_children source
  exact ((placeChild placeSource).withLoop context).bind fun _ =>
    ((valueChild valueSource).withLoop context).bind fun _ => generated_edge_emitEffect _ _ _

theorem cfg_source_assignOp {env : Core.TEnv} {results : List Ty} (op : BinOp) (place : Place)
    (expr : Expr) (origin : OriginId) (placeChild : CfgSourcePlace env results place)
    (valueChild : CfgSourceExpression env results expr) : CfgSourceStatement env results (.assignOp op place expr origin) := by
  intro output scope start finish source context
  obtain ⟨info, integer, childStart, placeSource, _, valueSource, _⟩ := tyStmt_assignOp_children source
  exact ((placeChild placeSource).withLoop context).bind fun _ => (generated_edge_emitDef _ _ _).bind fun _ =>
    ((valueChild valueSource).withLoop context).bind fun _ => (generated_edge_intTyOf _ _ _).bind fun _ =>
      (generated_edge_emitDef _ _ _).bind fun _ => generated_edge_emitEffect _ _ _

theorem cfg_source_rebind {env : Core.TEnv} {results : List Ty} (x : VarId) (expr : Expr) (origin : OriginId)
    (child : CfgSourceExpression env results expr) : CfgSourceStatement env results (.rebind x expr origin) := by
  intro output scope start finish source context
  obtain ⟨localVar, childTy, _, _, _, _, childSource, _⟩ := tyStmt_rebind_children source
  exact ((child childSource).withLoop context).bind fun value =>
    (generated_edge_coerceSlot _ _ x value origin).bind fun _ => (generated_edge_emitDef _ _ _).bind fun _ => generated_edge_emitEffect _ _ _

theorem cfg_source_append {env : Core.TEnv} {results : List Ty} (owner : Place) (view : View) (origin : OriginId)
    (ownerChild : CfgSourcePlace env results owner) (viewChild : CfgSourceView env results view) :
    CfgSourceStatement env results (.append owner view origin) := by
  intro output scope start finish source context
  obtain ⟨info, element, writable, childStart, ownerSource, _, viewSource, _⟩ := tyStmt_append_children source
  exact ((ownerChild ownerSource).withLoop context).bind fun _ =>
    ((viewChild viewSource).withLoop context).bind fun _ => generated_edge_emitEffect _ _ _

theorem cfg_source_popN {env : Core.TEnv} {results : List Ty} (owner : Place) (count : Expr) (origin : OriginId)
    (ownerChild : CfgSourcePlace env results owner) (countChild : CfgSourceExpression env results count) :
    CfgSourceStatement env results (.popN owner count origin) := by
  intro output scope start finish source context
  obtain ⟨info, element, integer, childStart, ownerSource, _, countSource, _⟩ := tyStmt_popN_children source
  exact ((ownerChild ownerSource).withLoop context).bind fun _ =>
    ((countChild countSource).withLoop context).bind fun _ => generated_edge_emitEffect _ _ _

theorem cfg_source_clear {env : Core.TEnv} {results : List Ty} (owner : Place) (origin : OriginId)
    (child : CfgSourcePlace env results owner) : CfgSourceStatement env results (.clear owner origin) := by
  intro output scope start finish source context
  obtain ⟨info, element, ownerSource, _⟩ := tyStmt_clear_children source
  exact ((child ownerSource).withLoop context).bind fun _ => generated_edge_emitEffect _ _ _

theorem cfg_source_resize {env : Core.TEnv} {results : List Ty} (owner : Place) (size : Expr)
    (fill : Option Expr) (origin : OriginId) (ownerChild : CfgSourcePlace env results owner)
    (sizeChild : CfgSourceExpression env results size)
    (fillChild : ∀ expr, fill = some expr → CfgSourceExpression env results expr) :
    CfgSourceStatement env results (.resize owner size fill origin) := by
  cases fill with
  | none =>
    intro output scope start finish source context
    obtain ⟨info, element, integer, childStart, sizeFinish, ownerSource, _, sizeSource, _, _⟩ := tyStmt_resize_children source
    exact ((ownerChild ownerSource).withLoop context).bind fun _ => ((sizeChild sizeSource).withLoop context).bind fun _ =>
      (generated_edge_pure _ _ _).bind fun _ => generated_edge_emitEffect _ _ _
  | some expr =>
    intro output scope start finish source context
    obtain ⟨info, element, integer, childStart, sizeFinish, ownerSource, _, sizeSource, fillSource, _⟩ := tyStmt_resize_children source
    exact ((ownerChild ownerSource).withLoop context).bind fun _ => ((sizeChild sizeSource).withLoop context).bind fun _ =>
      ((fillChild expr rfl fillSource).withLoop context).bind fun _ => generated_edge_emitEffect _ _ _

theorem cfg_source_assignWhole {env : Core.TEnv} {results : List Ty} (owner : Place) (expr : Expr) (origin : OriginId)
    (ownerChild : CfgSourcePlace env results owner) (valueChild : CfgSourceExpression env results expr) :
    CfgSourceStatement env results (.assignWhole owner expr origin) := by
  intro output scope start finish source context
  obtain ⟨info, element, childStart, ownerSource, _, valueSource, _⟩ := tyStmt_assignWhole_children source
  exact ((ownerChild ownerSource).withLoop context).bind fun _ => (generated_edge_emitEffect _ _ _).bind fun _ =>
    ((valueChild valueSource).withLoop context).bind fun _ => generated_edge_emitEffect _ _ _

end Goose.Lower.Validation

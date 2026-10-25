import Goose.Lower.Validation.CfgSourceEdgeContracts

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem cfg_source_variable (env : Core.TEnv) (results : List Ty) (index : VarId) :
    CfgSourcePlace env results (.var index) := by
  intro info start finish source
  exact generated_edge_emitDef _ _ _

theorem cfg_source_global (env : Core.TEnv) (results : List Ty) (index : GlobalId) :
    CfgSourcePlace env results (.global index) := by
  intro info start finish source
  exact generated_edge_emitDef _ _ _

theorem cfg_source_field {env : Core.TEnv} {results : List Ty} (owner : Place) (index : Nat)
    (child : CfgSourcePlace env results owner) : CfgSourcePlace env results (.field owner index) := by
  intro info start finish source
  obtain ⟨ownerInfo, ownerFinish, ownerSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (child ownerSource).bind fun _ => generated_edge_emitDef _ _ _

theorem cfg_source_dereference {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : CfgSourceExpression env results expr) : CfgSourcePlace env results (.deref expr) := by
  intro info start finish source
  cases special : Core.sliceRefTy env expr with
  | none =>
    obtain ⟨mu, childFinish, childSource⟩ := tyPlace_deref_child special source
    exact child childSource
  | some ty =>
    cases expr with
    | read place =>
      cases place with
      | var index =>
        exact (generated_edge_emitDef _ _ (.slotAddr index)).bind fun address =>
          (generated_edge_emitDef _ _ (.load address)).bind fun value =>
            (generated_edge_recordReadValueRootRecipe _ _ value (.var index)).bind fun _ =>
              generated_edge_pure _ _ value
      | _ => simp [Core.sliceRefTy] at special
    | _ => simp [Core.sliceRefTy] at special

theorem cfg_source_element {env : Core.TEnv} {results : List Ty} (view : View) (index : Expr) (origin : OriginId)
    (viewChild : CfgSourceView env results view) (indexChild : CfgSourceExpression env results index) :
    CfgSourcePlace env results (.elem view index origin) := by
  intro info start finish source
  obtain ⟨viewStart, viewFinish, indexFinish, writable, ty, viewSource, indexSource⟩ := tyPlace_elem_children source
  exact (viewChild viewSource).bind fun _ => (indexChild indexSource).bind fun _ => generated_edge_emitDef _ _ _

theorem cfg_source_ownerView {env : Core.TEnv} {results : List Ty} (place : Place)
    (child : CfgSourcePlace env results place) : CfgSourceView env results (.of place) := by
  intro info start finish source
  obtain ⟨placeInfo, placeFinish, placeSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (child placeSource).bind fun _ => generated_edge_emitDef _ _ _

theorem cfg_source_valueView {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : CfgSourceExpression env results expr) : CfgSourceView env results (.val expr) := by
  intro info start finish source
  obtain ⟨ty, childFinish, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (child childSource).bind fun _ => generated_edge_emitDef _ _ _

theorem cfg_source_omittedBound (env : Core.TEnv) (results : List Ty) : CfgSourceBound env results .omitted := by
  intro start finish source
  exact generated_edge_pure _ _ _

theorem cfg_source_expressionBound {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : CfgSourceExpression env results expr) : CfgSourceBound env results (.expr expr) := by
  intro start finish source
  obtain ⟨ty, childFinish, childSource⟩ := tyBound_child source
  exact (child childSource).bind fun _ => generated_edge_pure _ _ _

theorem cfg_source_endBound {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : CfgSourceExpression env results expr) : CfgSourceBound env results (.fromEnd expr) := by
  intro start finish source
  obtain ⟨ty, childFinish, childSource⟩ := tyBound_child source
  exact (child childSource).bind fun _ => generated_edge_pure _ _ _

theorem cfg_source_length {env : Core.TEnv} {results : List Ty} (view : View)
    (child : CfgSourceView env results view) : CfgSourceExpression env results (.len view) := by
  intro ty start finish source
  obtain ⟨info, childFinish, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (child childSource).bind fun _ => generated_edge_emitDef _ _ _

theorem cfg_source_slice {env : Core.TEnv} {results : List Ty} (mu : Mutability) (view : View)
    (lo hi : Bound) (origin : OriginId) (viewChild : CfgSourceView env results view)
    (loChild : CfgSourceBound env results lo) (hiChild : CfgSourceBound env results hi) :
    CfgSourceExpression env results (.slice mu view lo hi origin) := by
  intro ty start finish source
  obtain ⟨element, writable, viewStart, viewFinish, lowFinish, highFinish, viewSource, loSource, hiSource, _⟩ :=
    tyExpr_slice_children source
  exact (viewChild viewSource).bind fun _ => (loChild loSource).bind fun _ =>
    (hiChild hiSource).bind fun _ => generated_edge_emitDef _ _ _

theorem cfg_source_eachOwner {env : Core.TEnv} {results : List Ty} (place : Place)
    (child : CfgSourcePlace env results place) : CfgSourceEachSource env results (.of place) := by
  intro info start finish source
  obtain ⟨placeInfo, placeFinish, placeSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (child placeSource).bind fun _ => (generated_edge_emitDef _ _ _).bind fun _ => generated_edge_pure _ _ _

theorem cfg_source_eachValue {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : CfgSourceExpression env results expr) : CfgSourceEachSource env results (.val expr) := by
  intro info start finish source
  obtain ⟨ty, childFinish, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (child childSource).bind fun _ => (generated_edge_emitDef _ _ _).bind fun _ => generated_edge_pure _ _ _

end Goose.Lower.Validation

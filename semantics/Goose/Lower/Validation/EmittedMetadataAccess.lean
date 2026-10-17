import Goose.Lower.Validation.EmittedMetadataScalar

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem metadata_source_variable (env : Core.TEnv) (results : List Ty) (index : VarId) :
    EmittedMetadataSourcePlace env results (.var index) := by
  intro agreement info start finish source
  exact (EmittedMetadataAction.emitDef _ none (.slotAddr index)).metadata

theorem metadata_source_global (env : Core.TEnv) (results : List Ty) (index : GlobalId) :
    EmittedMetadataSourcePlace env results (.global index) := by
  intro agreement info start finish source
  exact (EmittedMetadataAction.emitDef _ none (.globalAddr index)).metadata

theorem metadata_source_read {env : Core.TEnv} {results : List Ty} (place : Place)
    (child : EmittedMetadataSourcePlace env results place) : EmittedMetadataSourceExpression env results (.read place) := by
  intro agreement type start finish source
  obtain ⟨info, childFinish, childSource, _⟩ := tyExpr_read_place source
  exact ((EmittedMetadataAction.lowerPlace place (child agreement childSource)).bind fun value =>
    EmittedMetadataAction.emitDef _ none (.load value)).metadata

theorem metadata_source_reference {env : Core.TEnv} {results : List Ty} (requested : Mutability) (place : Place)
    (child : EmittedMetadataSourcePlace env results place) : EmittedMetadataSourceExpression env results (.ref requested place) := by
  intro agreement type start finish source
  obtain ⟨info, childFinish, childSource, _, _⟩ := tyExpr_ref_place source
  exact ((EmittedMetadataAction.lowerPlace place (child agreement childSource)).bind fun value =>
    EmittedMetadataAction.borrowTo _ none requested value).metadata

theorem metadata_source_field {env : Core.TEnv} {results : List Ty} (owner : Place) (index : Nat)
    (child : EmittedMetadataSourcePlace env results owner) : EmittedMetadataSourcePlace env results (.field owner index) := by
  intro agreement info start finish source
  obtain ⟨ownerInfo, ownerFinish, ownerSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  exact ((EmittedMetadataAction.lowerPlace owner (child agreement ownerSource)).bind fun value =>
    EmittedMetadataAction.emitDef _ none (.fieldAddr value index)).metadata

theorem metadata_source_index {env : Core.TEnv} {results : List Ty} (view : View) (index : Expr) (origin : OriginId)
    (viewChild : EmittedMetadataSourceView env results view) (indexChild : EmittedMetadataSourceExpression env results index) :
    EmittedMetadataSourcePlace env results (.elem view index origin) := by
  intro agreement info start finish source
  obtain ⟨viewStart, viewFinish, indexFinish, writable, type, viewSource, indexSource⟩ := tyPlace_elem_children source
  exact ((EmittedMetadataAction.lowerView view (viewChild agreement viewSource)).bind fun vw =>
    (EmittedMetadataAction.lowerExpr index (indexChild agreement indexSource)).bind fun iv =>
      EmittedMetadataAction.emitDef _ none (.indexChecked vw iv (some origin))).metadata

theorem metadata_source_dereference {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : EmittedMetadataSourceExpression env results expr) : EmittedMetadataSourcePlace env results (.deref expr) := by
  intro agreement info start finish source
  cases special : Core.sliceRefTy env expr with
  | none =>
    obtain ⟨mu, childFinish, childSource⟩ := tyPlace_deref_child special source
    exact child agreement childSource
  | some type =>
    cases expr with
    | read place =>
      cases place with
      | var index =>
        exact ((EmittedMetadataAction.emitDef _ none (.slotAddr index)).bind fun value =>
          EmittedMetadataAction.emitDef _ none (.load value)).metadata
      | _ => simp [Core.sliceRefTy] at special
    | _ => simp [Core.sliceRefTy] at special

theorem metadata_source_view_of {env : Core.TEnv} {results : List Ty} (place : Place)
    (child : EmittedMetadataSourcePlace env results place) : EmittedMetadataSourceView env results (.of place) := by
  intro agreement element writable start finish source
  obtain ⟨info, childFinish, childSource, rest⟩ := (st_bind_ok _ _ _ _).mp source
  exact ((EmittedMetadataAction.lowerPlace place (child agreement childSource)).bind fun value =>
    EmittedMetadataAction.emitDef _ none (.snapshot
      (match (generalizing := false) place with | .var _ | .global _ => .owner | _ => .borrowed) value)).metadata

theorem metadata_source_view_val {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : EmittedMetadataSourceExpression env results expr) : EmittedMetadataSourceView env results (.val expr) := by
  intro agreement element writable start finish source
  obtain ⟨type, childFinish, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  exact ((EmittedMetadataAction.lowerExpr expr (child agreement childSource)).bind fun value =>
    EmittedMetadataAction.emitDef _ none (.sliceView value)).metadata

theorem metadata_source_length {env : Core.TEnv} {results : List Ty} (view : View)
    (child : EmittedMetadataSourceView env results view) : EmittedMetadataSourceExpression env results (.len view) := by
  intro agreement type start finish source
  obtain ⟨pair, childFinish, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact ((EmittedMetadataAction.lowerView view (child agreement childSource)).bind fun value =>
    EmittedMetadataAction.emitDef _ none (.viewLen value)).metadata


end Goose.Lower.Validation

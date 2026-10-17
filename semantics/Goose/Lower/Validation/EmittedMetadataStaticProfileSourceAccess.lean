import Goose.Lower.Validation.EmittedMetadataStaticProfileSourceScalar

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem profile_source_variable (env : Core.TEnv) (results : List Ty) (index : VarId) :
    EmittedProfileSourcePlace env results (.var index) := by
  intro info start finish source
  exact (EmittedProfileRun.emitDef (.slotAddr index) (by intro; trivial))

theorem profile_source_global (env : Core.TEnv) (results : List Ty) (index : GlobalId) :
    EmittedProfileSourcePlace env results (.global index) := by
  intro info start finish source
  exact (EmittedProfileRun.emitDef (.globalAddr index) (by intro; trivial))

theorem profile_source_read {env : Core.TEnv} {results : List Ty} (place : Place)
    (child : EmittedProfileSourcePlace env results place) : EmittedProfileSourceExpression env results (.read place) := by
  intro type start finish source
  obtain ⟨info, childFinish, childSource, _⟩ := tyExpr_read_place source
  exact ((child childSource).bind fun value =>
    EmittedProfileRun.emitDef (.load value) (by intro; trivial))

theorem profile_source_reference {env : Core.TEnv} {results : List Ty} (requested : Mutability) (place : Place)
    (child : EmittedProfileSourcePlace env results place) : EmittedProfileSourceExpression env results (.ref requested place) := by
  intro type start finish source
  obtain ⟨info, childFinish, childSource, _, _⟩ := tyExpr_ref_place source
  exact ((child childSource).bind fun value =>
    EmittedProfileRun.borrowTo requested value)

theorem profile_source_field {env : Core.TEnv} {results : List Ty} (owner : Place) (index : Nat)
    (child : EmittedProfileSourcePlace env results owner) : EmittedProfileSourcePlace env results (.field owner index) := by
  intro info start finish source
  have profile := static_tyPlace_field_profile source
  obtain ⟨ownerInfo, ownerFinish, ownerSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  exact ((child ownerSource).bind fun value =>
    EmittedProfileRun.emitDef (.fieldAddr value index) (fun _ => profile))

theorem profile_source_index {env : Core.TEnv} {results : List Ty} (view : View) (index : Expr) (origin : OriginId)
    (viewChild : EmittedProfileSourceView env results view) (indexChild : EmittedProfileSourceExpression env results index) :
    EmittedProfileSourcePlace env results (.elem view index origin) := by
  intro info start finish source
  obtain ⟨viewStart, viewFinish, indexFinish, writable, type, viewSource, indexSource⟩ := tyPlace_elem_children source
  exact ((viewChild viewSource).bind fun vw =>
    (indexChild indexSource).bind fun iv =>
      EmittedProfileRun.emitDef (.indexChecked vw iv (some origin)) (by intro; trivial))

theorem profile_source_dereference {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : EmittedProfileSourceExpression env results expr) : EmittedProfileSourcePlace env results (.deref expr) := by
  intro info start finish source
  cases special : Core.sliceRefTy env expr with
  | none =>
    obtain ⟨mu, childFinish, childSource⟩ := tyPlace_deref_child special source
    exact child childSource
  | some type =>
    cases expr with
    | read place =>
      cases place with
      | var index =>
        exact ((EmittedProfileRun.emitDef (.slotAddr index) (by intro; trivial)).bind fun value =>
          EmittedProfileRun.emitDef (.load value) (by intro; trivial))
      | _ => simp [Core.sliceRefTy] at special
    | _ => simp [Core.sliceRefTy] at special

theorem profile_source_view_of {env : Core.TEnv} {results : List Ty} (place : Place)
    (child : EmittedProfileSourcePlace env results place) : EmittedProfileSourceView env results (.of place) := by
  intro element writable start finish source
  obtain ⟨info, childFinish, childSource, rest⟩ := (st_bind_ok _ _ _ _).mp source
  exact ((child childSource).bind fun value =>
    EmittedProfileRun.emitDef (.snapshot
      (match (generalizing := false) place with | .var _ | .global _ => .owner | _ => .borrowed) value) (by intro; trivial))

theorem profile_source_view_val {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : EmittedProfileSourceExpression env results expr) : EmittedProfileSourceView env results (.val expr) := by
  intro element writable start finish source
  obtain ⟨type, childFinish, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  exact ((child childSource).bind fun value =>
    EmittedProfileRun.emitDef (.sliceView value) (by intro; trivial))

theorem profile_source_length {env : Core.TEnv} {results : List Ty} (view : View)
    (child : EmittedProfileSourceView env results view) : EmittedProfileSourceExpression env results (.len view) := by
  intro type start finish source
  obtain ⟨pair, childFinish, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact ((child childSource).bind fun value =>
    EmittedProfileRun.emitDef (.viewLen value) (by intro; trivial))


end Goose.Lower.Validation

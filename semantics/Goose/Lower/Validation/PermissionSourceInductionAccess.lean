import Goose.Lower.Validation.PermissionSourceInductionScalar
import Goose.Lower.Validation.PermissionPreservationSnapshots
import Goose.Lower.Validation.DereferenceTyping
import Goose.Lower.Validation.ViewTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem permission_source_variable (env : Core.TEnv) (func : Func) (results : List Ty) (index : Nat) :
    PermissionStoragePlaceChild env func results (.var index) := by
  intro info start finish source before after value generated run
  exact newPermissions_lowerPlace_var run

theorem permission_source_global (env : Core.TEnv) (func : Func) (results : List Ty) (index : Nat) :
    PermissionStoragePlaceChild env func results (.global index) := by
  intro info start finish source before after value generated run
  exact newPermissions_lowerPlace_global run

theorem permission_source_read {env : Core.TEnv} {func : Func} {results : List Ty}
    (place : Place) (child : PermissionStoragePlaceChild env func results place) :
    PermissionStorageExprChild env func results (.read place) := by
  intro result start finish source before after value generated run
  obtain ⟨info, childFinish, childSource, _⟩ := tyExpr_read_place source
  obtain ⟨childValue, middle, childRun, remaining⟩ := bind_eq.mp run
  exact newPermissions_lowerExpr_read childRun (child childSource generated childRun) generated run

theorem permission_source_length {env : Core.TEnv} {func : Func} {results : List Ty}
    (view : View) (child : PermissionStorageViewChild env func results view) :
    PermissionStorageExprChild env func results (.len view) := by
  intro result start finish source before after value generated run
  obtain ⟨pair, childFinish, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨childValue, middle, childRun, remaining⟩ := bind_eq.mp run
  exact newPermissions_lowerExpr_len childRun (child childSource generated childRun) generated run

theorem permission_source_reference {env : Core.TEnv} {func : Func} {results : List Ty}
    (requested : Mutability) (place : Place) (child : PermissionStoragePlaceChild env func results place) :
    PermissionStorageExprChild env func results (.ref requested place) := by
  intro result start finish source before after value generated run
  exact newPermissions_lowerExpr_ref source (Nat.le_refl _)
    (fun info next typed before middle owner generated lowered => child typed generated lowered) generated run

theorem permission_source_field {env : Core.TEnv} {func : Func} {results : List Ty}
    (owner : Place) (index : Nat) (child : PermissionStoragePlaceChild env func results owner) :
    PermissionStoragePlaceChild env func results (.field owner index) := by
  intro info start finish source before after value generated run
  obtain ⟨ownerInfo, ownerFinish, ownerSource, remaining⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨ownerValue, middle, ownerRun, remaining⟩ := bind_eq.mp run
  exact newPermissions_lowerPlace_field ownerRun (child ownerSource generated ownerRun) generated run

theorem permission_source_index {env : Core.TEnv} {func : Func} {results : List Ty}
    (view : View) (index : Expr) (origin : OriginId)
    (viewChild : PermissionStorageViewChild env func results view)
    (indexChild : PermissionStorageExprChild env func results index) :
    PermissionStoragePlaceChild env func results (.elem view index origin) := by
  intro info start finish source before after value generated run
  obtain ⟨viewStart, viewFinish, indexFinish, writable, type, viewSource, indexSource⟩ := tyPlace_elem_children source
  obtain ⟨viewValue, viewed, viewRun, remaining⟩ := bind_eq.mp run
  obtain ⟨indexValue, middle, indexRun, remaining⟩ := bind_eq.mp remaining
  exact newPermissions_lowerPlace_elem viewRun indexRun (viewChild viewSource generated viewRun)
    ((indexChild indexSource (generated.lowerView view viewRun) indexRun).weaken
      (advB_lowerView view _ _ _ _ viewRun).vals) generated run

theorem permission_source_dereference {env : Core.TEnv} {func : Func} {results : List Ty}
    (expr : Expr) (child : PermissionStorageExprChild env func results expr) :
    PermissionStoragePlaceChild env func results (.deref expr) := by
  intro info start finish source before after value generated run
  cases special : Core.sliceRefTy env expr with
  | none =>
    obtain ⟨mu, childFinish, childSource⟩ := tyPlace_deref_child special source
    cases expr <;> exact child childSource generated run
  | some type =>
    cases expr with
    | read place =>
      cases place with
      | var index => exact newPermissions_lowerPlace_deref_refSlice generated run
      | _ => simp [Core.sliceRefTy] at special
    | _ => simp [Core.sliceRefTy] at special

theorem permission_source_view_of {env : Core.TEnv} {func : Func} {results : List Ty}
    (place : Place) (child : PermissionStoragePlaceChild env func results place) :
    PermissionStorageViewChild env func results (.of place) := by
  intro element writable start finish source before after value generated run
  obtain ⟨info, childFinish, childSource, rest⟩ := (st_bind_ok _ _ _ _).mp source
  exact lowerView_of_newPermissionInstructions place childSource run generated
    (fun owner middle lowered => child childSource generated lowered)

theorem permission_source_view_val {env : Core.TEnv} {func : Func} {results : List Ty}
    (expr : Expr) (child : PermissionStorageExprChild env func results expr) :
    PermissionStorageViewChild env func results (.val expr) := by
  intro element writable start finish source before after value generated run
  obtain ⟨type, childFinish, childSource, remaining⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨childValue, middle, childRun, remaining⟩ := bind_eq.mp run
  exact newPermissions_lowerView_val childRun (child childSource generated childRun) generated run

#print axioms permission_source_variable
#print axioms permission_source_global
#print axioms permission_source_read
#print axioms permission_source_length
#print axioms permission_source_reference
#print axioms permission_source_field
#print axioms permission_source_index
#print axioms permission_source_dereference
#print axioms permission_source_view_of
#print axioms permission_source_view_val

end Goose.Lower.Validation

import Goose.Lower.Validation.StorageWalkSourceScalar

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem storageWalk_source_variable (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) (index : VarId) :
    StorageWalkSourcePlace env results stack (.var index) := by
  intro info start finish source visible loop
  obtain ⟨localVar, next, lookup, remaining⟩ := (st_bind_ok _ _ _ _).mp source
  have member := (varOf_ok _ _ _ _).mp lookup |>.1
  exact StorageWalkAction.emitDef _ stack loop (.slotAddr index)
    (fun _ descriptor row => storageWalk_visible_slot visible member results row)

theorem storageWalk_source_global (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) (index : GlobalId) :
    StorageWalkSourcePlace env results stack (.global index) := by
  intro info start finish source visible loop
  exact StorageWalkAction.emitDef _ stack loop (.globalAddr index) (by simp [StorageInstructionVisible])

theorem storageWalk_source_read {env : Core.TEnv} {results : List Ty} {stack : List ScopeId} (place : Place)
    (child : StorageWalkSourcePlace env results stack place) : StorageWalkSourceExpression env results stack (.read place) := by
  intro type start finish source visible loop
  obtain ⟨info, childFinish, childSource, _⟩ := tyExpr_read_place source
  exact (child childSource visible loop).bind fun value =>
    (StorageWalkAction.emitDef _ stack loop (.load value) (by simp [StorageInstructionVisible])).bind fun loaded =>
      (StorageWalkAction.recordReadValueRootRecipe _ stack loop loaded place).bind fun _ =>
        StorageWalkAction.pure _ stack loop loaded

theorem storageWalk_source_reference {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (requested : Mutability) (place : Place) (child : StorageWalkSourcePlace env results stack place) :
    StorageWalkSourceExpression env results stack (.ref requested place) := by
  intro type start finish source visible loop
  obtain ⟨info, childFinish, childSource, _, _⟩ := tyExpr_ref_place source
  exact (child childSource visible loop).bind fun value => StorageWalkAction.borrowTo _ stack loop requested value

theorem storageWalk_source_field {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (owner : Place) (index : Nat) (child : StorageWalkSourcePlace env results stack owner) :
    StorageWalkSourcePlace env results stack (.field owner index) := by
  intro info start finish source visible loop
  obtain ⟨ownerInfo, ownerFinish, ownerSource, remaining⟩ := (st_bind_ok _ _ _ _).mp source
  exact (child ownerSource visible loop).bind fun value =>
    StorageWalkAction.emitDef _ stack loop (.fieldAddr value index) (by simp [StorageInstructionVisible])

theorem storageWalk_source_index {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (view : View) (index : Expr) (origin : OriginId)
    (viewChild : StorageWalkSourceView env results stack view) (indexChild : StorageWalkSourceExpression env results stack index) :
    StorageWalkSourcePlace env results stack (.elem view index origin) := by
  intro info start finish source visible loop
  obtain ⟨viewStart, viewFinish, indexFinish, writable, type, viewSource, indexSource⟩ := tyPlace_elem_children source
  exact (viewChild viewSource visible loop).bind fun vw =>
    (indexChild indexSource visible loop).bind fun iv =>
      StorageWalkAction.emitDef _ stack loop (.indexChecked vw iv (some origin)) (by simp [StorageInstructionVisible])

theorem storageWalk_source_dereference {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (expr : Expr) (child : StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourcePlace env results stack (.deref expr) := by
  intro info start finish source visible loop
  cases special : Core.sliceRefTy env expr with
  | none =>
    obtain ⟨mu, childFinish, childSource⟩ := tyPlace_deref_child special source
    exact child childSource visible loop
  | some type =>
    cases expr with
    | read place =>
      cases place with
      | var index =>
        exact (StorageWalkAction.emitDef _ stack loop (.slotAddr index)
          (fun _ descriptor row => storageWalk_visible_slot visible (storageWalk_sliceRef_visible special) results row)).bind fun value =>
            (StorageWalkAction.emitDef _ stack loop (.load value) (by simp [StorageInstructionVisible])).bind fun loaded =>
              (StorageWalkAction.recordReadValueRootRecipe _ stack loop loaded (.var index)).bind fun _ =>
                StorageWalkAction.pure _ stack loop loaded
      | _ => simp [Core.sliceRefTy] at special
    | _ => simp [Core.sliceRefTy] at special

theorem storageWalk_source_view_of {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (place : Place) (child : StorageWalkSourcePlace env results stack place) :
    StorageWalkSourceView env results stack (.of place) := by
  intro element writable start finish source visible loop
  obtain ⟨info, childFinish, childSource, remaining⟩ := (st_bind_ok _ _ _ _).mp source
  exact (child childSource visible loop).bind fun value =>
    StorageWalkAction.emitDef _ stack loop (.snapshot
      (match (generalizing := false) place with | .var _ | .global _ => .owner | _ => .borrowed) value)
      (by simp [StorageInstructionVisible])

theorem storageWalk_source_view_val {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (expr : Expr) (child : StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceView env results stack (.val expr) := by
  intro element writable start finish source visible loop
  obtain ⟨type, childFinish, childSource, remaining⟩ := (st_bind_ok _ _ _ _).mp source
  exact (child childSource visible loop).bind fun value =>
    StorageWalkAction.emitDef _ stack loop (.sliceView value) (by simp [StorageInstructionVisible])

theorem storageWalk_source_length {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (view : View) (child : StorageWalkSourceView env results stack view) :
    StorageWalkSourceExpression env results stack (.len view) := by
  intro type start finish source visible loop
  obtain ⟨pair, childFinish, childSource, remaining⟩ := (st_bind_ok _ _ _ _).mp source
  exact (child childSource visible loop).bind fun value =>
    StorageWalkAction.emitDef _ stack loop (.viewLen value) (by simp [StorageInstructionVisible])

theorem storageWalk_source_eachSource_of {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (place : Place) (child : StorageWalkSourcePlace env results stack place) :
    StorageWalkSourceEachSource env results stack (.of place) := by
  intro element writable start finish source visible loop
  obtain ⟨info, childFinish, childSource, remaining⟩ := (st_bind_ok _ _ _ _).mp source
  exact (child childSource visible loop).bind fun owner =>
    (StorageWalkAction.emitDef _ stack loop (.snapshot
      (match (generalizing := false) place with | .var _ | .global _ => .owner | _ => .borrowed) owner)
      (by simp [StorageInstructionVisible])).bind fun view =>
        StorageWalkAction.pure _ stack loop (some owner, view)

theorem storageWalk_source_eachSource_val {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (expr : Expr) (child : StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceEachSource env results stack (.val expr) := by
  intro element writable start finish source visible loop
  obtain ⟨type, childFinish, childSource, remaining⟩ := (st_bind_ok _ _ _ _).mp source
  exact (child childSource visible loop).bind fun value =>
    (StorageWalkAction.emitDef _ stack loop (.sliceView value) (by simp [StorageInstructionVisible])).bind fun view =>
      StorageWalkAction.pure _ stack loop (none, view)

#print axioms storageWalk_source_variable
#print axioms storageWalk_source_global
#print axioms storageWalk_source_read
#print axioms storageWalk_source_reference
#print axioms storageWalk_source_field
#print axioms storageWalk_source_index
#print axioms storageWalk_source_dereference
#print axioms storageWalk_source_view_of
#print axioms storageWalk_source_view_val
#print axioms storageWalk_source_length
#print axioms storageWalk_source_eachSource_of
#print axioms storageWalk_source_eachSource_val

end Goose.Lower.Validation

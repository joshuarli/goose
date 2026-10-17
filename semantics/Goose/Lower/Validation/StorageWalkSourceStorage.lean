import Goose.Lower.Validation.StorageWalkSourceCollections

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem storageWalk_source_let {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (slot : VarId) (expr : Expr) (origin : OriginId)
    (child : StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceStatement env results stack scope (.letS slot expr origin) := by
  intro output start finish source visible active loop
  obtain ⟨localVar, type, next, declared, childSource, passing, _⟩ := tyStmt_let_children source
  exact (child childSource visible loop).bind fun value =>
    (StorageWalkAction.coerceSlot _ stack loop slot value origin).bind fun coerced =>
      StorageWalkAction.emitEffect _ stack loop (.slotInit slot coerced (some origin)) rfl
        (fun descriptor row => storageWalk_declared_slot active declared results row)

theorem storageWalk_source_rebind {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (slot : VarId) (expr : Expr) (origin : OriginId)
    (child : StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceStatement env results stack scope (.rebind slot expr origin) := by
  intro output start finish source visible active loop
  obtain ⟨localVar, type, localRow, member, reference, writable, childSource, passing, _⟩ := tyStmt_rebind_children source
  exact (child childSource visible loop).bind fun value =>
    (StorageWalkAction.coerceSlot _ stack loop slot value origin).bind fun coerced =>
      (StorageWalkAction.emitDef _ stack loop (.slotAddr slot)
        (fun _ descriptor row => storageWalk_visible_slot visible member results row)).bind fun address =>
          StorageWalkAction.emitEffect _ stack loop (.store address coerced (some origin)) rfl (by trivial)

theorem storageWalk_source_assign {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : StorageWalkSourcePlace env results stack place)
    (exprChild : StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceStatement env results stack scope (.assign place expr origin) := by
  intro output start finish source visible active loop
  obtain ⟨info, next, placeSource, exprSource, copyable, binding, _⟩ := tyStmt_assign_children source
  exact (placeChild placeSource visible loop).bind fun address =>
    (exprChild exprSource visible loop).bind fun value =>
      StorageWalkAction.emitEffect _ stack loop (.store address value (some origin)) rfl (by trivial)

theorem storageWalk_source_assignOp {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (op : BinOp) (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : StorageWalkSourcePlace env results stack place)
    (exprChild : StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceStatement env results stack scope (.assignOp op place expr origin) := by
  intro output start finish source visible active loop
  obtain ⟨info, integer, next, placeSource, shape, exprSource, binding, _⟩ := tyStmt_assignOp_children source
  exact (placeChild placeSource visible loop).bind fun address =>
    (StorageWalkAction.emitDef _ stack loop (.load address) (by intro result; trivial)).bind fun old =>
      (exprChild exprSource visible loop).bind fun value =>
        (StorageWalkAction.intTyOf _ stack loop old).bind fun integer =>
          (StorageWalkAction.emitDef _ stack loop (.bin op integer old value (some origin)) (by intro result; trivial)).bind fun result =>
            StorageWalkAction.emitEffect _ stack loop (.store address result (some origin)) rfl (by trivial)

theorem storageWalk_source_append {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (place : Place) (view : View) (origin : OriginId)
    (placeChild : StorageWalkSourcePlace env results stack place) (viewChild : StorageWalkSourceView env results stack view) :
    StorageWalkSourceStatement env results stack scope (.append place view origin) := by
  intro output start finish source visible active loop
  obtain ⟨info, element, writable, next, placeSource, ownerType, viewSource, permission, _⟩ := tyStmt_append_children source
  exact (placeChild placeSource visible loop).bind fun address =>
    (viewChild viewSource visible loop).bind fun value =>
      StorageWalkAction.emitEffect _ stack loop (.append address value (some origin)) rfl (by trivial)

theorem storageWalk_source_popN {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : StorageWalkSourcePlace env results stack place) (exprChild : StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceStatement env results stack scope (.popN place expr origin) := by
  intro output start finish source visible active loop
  obtain ⟨info, element, integer, next, placeSource, ownerType, exprSource, permission, _⟩ := tyStmt_popN_children source
  exact (placeChild placeSource visible loop).bind fun address =>
    (exprChild exprSource visible loop).bind fun value =>
      StorageWalkAction.emitEffect _ stack loop (.popN address value (some origin)) rfl (by trivial)

theorem storageWalk_source_clear {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (place : Place) (origin : OriginId) (child : StorageWalkSourcePlace env results stack place) :
    StorageWalkSourceStatement env results stack scope (.clear place origin) := by
  intro output start finish source visible active loop
  obtain ⟨info, element, placeSource, ownerType, permission, _⟩ := tyStmt_clear_children source
  exact (child placeSource visible loop).bind fun address =>
    StorageWalkAction.emitEffect _ stack loop (.clear address (some origin)) rfl (by trivial)

theorem storageWalk_source_assignWhole {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : StorageWalkSourcePlace env results stack place) (exprChild : StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceStatement env results stack scope (.assignWhole place expr origin) := by
  intro output start finish source visible active loop
  obtain ⟨info, element, next, placeSource, shape, exprSource, binding, contents, _⟩ := tyStmt_assignWhole_children source
  exact (placeChild placeSource visible loop).bind fun address =>
    (StorageWalkAction.emitEffect _ stack loop (.clear address (some origin)) rfl (by trivial)).bind fun _ =>
      (exprChild exprSource visible loop).bind fun value =>
        StorageWalkAction.emitEffect _ stack loop (.replace address value (some origin)) rfl (by trivial)

theorem storageWalk_source_resize {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (place : Place) (size : Expr) (fill : Option Expr) (origin : OriginId)
    (placeChild : StorageWalkSourcePlace env results stack place) (sizeChild : StorageWalkSourceExpression env results stack size)
    (fillChild : ∀ expr, fill = some expr → StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceStatement env results stack scope (.resize place size fill origin) := by
  cases fill with
  | none =>
    intro output start finish source visible active loop
    obtain ⟨info, element, integer, next, sizeFinish, placeSource, ownerType, sizeSource, fillSource, permission, _⟩ :=
      tyStmt_resize_children source
    exact (placeChild placeSource visible loop).bind fun address =>
      (sizeChild sizeSource visible loop).bind fun count =>
        StorageWalkAction.emitEffect _ stack loop (.resize address count none (some origin)) rfl (by trivial)
  | some expr =>
    intro output start finish source visible active loop
    obtain ⟨info, element, integer, next, sizeFinish, placeSource, ownerType, sizeSource, fillSource, permission, _⟩ :=
      tyStmt_resize_children source
    exact (placeChild placeSource visible loop).bind fun address =>
      (sizeChild sizeSource visible loop).bind fun count =>
        (fillChild expr rfl fillSource visible loop).bind fun value =>
          StorageWalkAction.emitEffect _ stack loop (.resize address count (some value) (some origin)) rfl (by trivial)

#print axioms storageWalk_source_let
#print axioms storageWalk_source_rebind
#print axioms storageWalk_source_assign
#print axioms storageWalk_source_assignOp
#print axioms storageWalk_source_append
#print axioms storageWalk_source_popN
#print axioms storageWalk_source_clear
#print axioms storageWalk_source_assignWhole
#print axioms storageWalk_source_resize

end Goose.Lower.Validation

import Goose.Lower.Validation.SnapshotContentsSourceLeavesCollections
import Goose.Lower.Validation.SourceStatementTypingStorage

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem snapshot_source_let {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (slot : SlotId) (expr : Expr) (origin : OriginId)
    (child : SnapshotSourceExpression env results expr) : SnapshotSourceStatement env results scope (.letS slot expr origin) := by
  intro output start finish source loop
  obtain ⟨localVar, type, childStart, declared, childSource, passable, _⟩ := tyStmt_let_children source
  exact (((SnapshotSourceAction.lowerExpr expr (child childSource)).withLoop loop).bind fun value =>
    (SnapshotSourceAction.coerceSlot _ loop slot value origin).bind fun value =>
      SnapshotSourceAction.emitEffect _ loop (.slotInit slot value (some origin))).snapshots

theorem snapshot_source_rebind {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (slot : SlotId) (expr : Expr) (origin : OriginId)
    (child : SnapshotSourceExpression env results expr) : SnapshotSourceStatement env results scope (.rebind slot expr origin) := by
  intro output start finish source loop
  obtain ⟨localVar, type, localRow, _, _, _, childSource, _, _⟩ := tyStmt_rebind_children source
  exact (((SnapshotSourceAction.lowerExpr expr (child childSource)).withLoop loop).bind fun value =>
    (SnapshotSourceAction.coerceSlot _ loop slot value origin).bind fun value =>
      (SnapshotSourceAction.emitDef _ loop (.slotAddr slot) (by intros; intro h; cases h)).bind fun address =>
        SnapshotSourceAction.emitEffect _ loop (.store address value (some origin))).snapshots

theorem snapshot_source_assign {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : SnapshotSourcePlace env results place) (exprChild : SnapshotSourceExpression env results expr) : SnapshotSourceStatement env results scope (.assign place expr origin) := by
  intro output start finish source loop
  obtain ⟨info, childStart, placeSource, exprSource, _, _, _⟩ := tyStmt_assign_children source
  exact (((SnapshotSourceAction.lowerPlace place (placeChild placeSource)).withLoop loop).bind fun address =>
    ((SnapshotSourceAction.lowerExpr expr (exprChild exprSource)).withLoop loop).bind fun value =>
      SnapshotSourceAction.emitEffect _ loop (.store address value (some origin))).snapshots

theorem snapshot_source_assignOp {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (op : BinOp) (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : SnapshotSourcePlace env results place) (exprChild : SnapshotSourceExpression env results expr) : SnapshotSourceStatement env results scope (.assignOp op place expr origin) := by
  intro output start finish source loop
  obtain ⟨info, integer, childStart, placeSource, infoType, exprSource, _, _⟩ := tyStmt_assignOp_children source
  exact (((SnapshotSourceAction.lowerPlace place (placeChild placeSource)).withLoop loop).bind fun address =>
    (SnapshotSourceAction.emitDef _ loop (.load address) (by intros; intro h; cases h)).bind fun old =>
      ((SnapshotSourceAction.lowerExpr expr (exprChild exprSource)).withLoop loop).bind fun rhs =>
        (SnapshotSourceAction.intTyOf _ loop old).bind fun type =>
          (SnapshotSourceAction.emitDef _ loop (.bin op type old rhs (some origin)) (by intros; intro h; cases h)).bind fun value =>
            SnapshotSourceAction.emitEffect _ loop (.store address value (some origin))).snapshots

theorem snapshot_source_clear {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (origin : OriginId)
    (child : SnapshotSourcePlace env results place) : SnapshotSourceStatement env results scope (.clear place origin) := by
  intro output start finish source loop
  obtain ⟨info, element, childSource, _, _, _⟩ := tyStmt_clear_children source
  exact (((SnapshotSourceAction.lowerPlace place (child childSource)).withLoop loop).bind fun address =>
    SnapshotSourceAction.emitEffect _ loop (.clear address (some origin))).snapshots

theorem snapshot_source_append {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (view : View) (origin : OriginId)
    (placeChild : SnapshotSourcePlace env results place) (viewChild : SnapshotSourceView env results view) : SnapshotSourceStatement env results scope (.append place view origin) := by
  intro output start finish source loop
  obtain ⟨info, element, writable, childStart, placeSource, _, viewSource, _, _⟩ := tyStmt_append_children source
  exact (((SnapshotSourceAction.lowerPlace place (placeChild placeSource)).withLoop loop).bind fun address =>
    ((SnapshotSourceAction.lowerView view (viewChild viewSource)).withLoop loop).bind fun value =>
      SnapshotSourceAction.emitEffect _ loop (.append address value (some origin))).snapshots

theorem snapshot_source_popN {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : SnapshotSourcePlace env results place) (exprChild : SnapshotSourceExpression env results expr) : SnapshotSourceStatement env results scope (.popN place expr origin) := by
  intro output start finish source loop
  obtain ⟨info, element, integer, childStart, placeSource, _, exprSource, _, _⟩ := tyStmt_popN_children source
  exact (((SnapshotSourceAction.lowerPlace place (placeChild placeSource)).withLoop loop).bind fun address =>
    ((SnapshotSourceAction.lowerExpr expr (exprChild exprSource)).withLoop loop).bind fun value =>
      SnapshotSourceAction.emitEffect _ loop (.popN address value (some origin))).snapshots

theorem snapshot_source_assignWhole {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : SnapshotSourcePlace env results place) (exprChild : SnapshotSourceExpression env results expr) : SnapshotSourceStatement env results scope (.assignWhole place expr origin) := by
  intro output start finish source loop
  obtain ⟨info, element, childStart, placeSource, _, exprSource, _, _, _⟩ := tyStmt_assignWhole_children source
  exact (((SnapshotSourceAction.lowerPlace place (placeChild placeSource)).withLoop loop).bind fun address =>
    (SnapshotSourceAction.emitEffect _ loop (.clear address (some origin))).bind fun _ =>
      ((SnapshotSourceAction.lowerExpr expr (exprChild exprSource)).withLoop loop).bind fun value =>
        SnapshotSourceAction.emitEffect _ loop (.replace address value (some origin))).snapshots

theorem snapshot_source_resize {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (size : Expr) (fill : Option Expr) (origin : OriginId)
    (placeChild : SnapshotSourcePlace env results place) (sizeChild : SnapshotSourceExpression env results size)
    (fillChild : ∀ expr, fill = some expr → SnapshotSourceExpression env results expr) :
    SnapshotSourceStatement env results scope (.resize place size fill origin) := by
  intro output start finish source loop
  obtain ⟨info, element, integer, childStart, sizeFinish, placeSource, _, sizeSource, fillSource, _, _⟩ :=
    tyStmt_resize_children source
  cases fill with
  | none =>
    exact (((SnapshotSourceAction.lowerPlace place (placeChild placeSource)).withLoop loop).bind fun address =>
      ((SnapshotSourceAction.lowerExpr size (sizeChild sizeSource)).withLoop loop).bind fun count =>
        (SnapshotSourceAction.pure _ loop none).bind fun value =>
          SnapshotSourceAction.emitEffect _ loop (.resize address count value (some origin))).snapshots
  | some expr =>
    exact (((SnapshotSourceAction.lowerPlace place (placeChild placeSource)).withLoop loop).bind fun address =>
      ((SnapshotSourceAction.lowerExpr size (sizeChild sizeSource)).withLoop loop).bind fun count =>
        (((SnapshotSourceAction.lowerExpr expr (fillChild expr rfl fillSource)).withLoop loop).bind
          (fun value => SnapshotSourceAction.pure _ loop (some value))).bind fun value =>
            SnapshotSourceAction.emitEffect _ loop (.resize address count value (some origin))).snapshots

end Goose.Lower.Validation

import Goose.Lower.Validation.SnapshotContentsSourceLeavesScalar

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem snapshot_source_variable (env : Core.TEnv) (results : List Ty) (index : VarId) :
    SnapshotSourcePlace env results (.var index) := by
  intro info start finish source
  exact (SnapshotSourceAction.emitDef _ none (.slotAddr index) (by intros; intro h; cases h)).snapshots

theorem snapshot_source_global (env : Core.TEnv) (results : List Ty) (index : GlobalId) :
    SnapshotSourcePlace env results (.global index) := by
  intro info start finish source
  exact (SnapshotSourceAction.emitDef _ none (.globalAddr index) (by intros; intro h; cases h)).snapshots

theorem snapshot_source_read {env : Core.TEnv} {results : List Ty} (place : Place)
    (child : SnapshotSourcePlace env results place) : SnapshotSourceExpression env results (.read place) := by
  intro type start finish source
  obtain ⟨info, childFinish, childSource, _⟩ := tyExpr_read_place source
  exact ((SnapshotSourceAction.lowerPlace place (child childSource)).bind fun value =>
    (SnapshotSourceAction.emitDef _ none (.load value) (by intros; intro h; cases h)).bind fun loaded =>
      (SnapshotSourceAction.recordReadValueRootRecipe _ none loaded place).bind fun _ =>
        SnapshotSourceAction.pure _ none loaded).snapshots

theorem snapshot_source_reference {env : Core.TEnv} {results : List Ty} (requested : Mutability) (place : Place)
    (child : SnapshotSourcePlace env results place) : SnapshotSourceExpression env results (.ref requested place) := by
  intro type start finish source
  obtain ⟨info, childFinish, childSource, _, _⟩ := tyExpr_ref_place source
  exact ((SnapshotSourceAction.lowerPlace place (child childSource)).bind fun value =>
    SnapshotSourceAction.borrowTo _ none requested value).snapshots

theorem snapshot_source_field {env : Core.TEnv} {results : List Ty} (owner : Place) (index : Nat)
    (child : SnapshotSourcePlace env results owner) : SnapshotSourcePlace env results (.field owner index) := by
  intro info start finish source
  obtain ⟨ownerInfo, ownerFinish, ownerSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  exact ((SnapshotSourceAction.lowerPlace owner (child ownerSource)).bind fun value =>
    SnapshotSourceAction.emitDef _ none (.fieldAddr value index) (by intros; intro h; cases h)).snapshots

theorem snapshot_source_index {env : Core.TEnv} {results : List Ty} (view : View) (index : Expr) (origin : OriginId)
    (viewChild : SnapshotSourceView env results view) (indexChild : SnapshotSourceExpression env results index) :
    SnapshotSourcePlace env results (.elem view index origin) := by
  intro info start finish source
  obtain ⟨viewStart, viewFinish, indexFinish, writable, type, viewSource, indexSource⟩ := tyPlace_elem_children source
  exact ((SnapshotSourceAction.lowerView view (viewChild viewSource)).bind fun vw =>
    (SnapshotSourceAction.lowerExpr index (indexChild indexSource)).bind fun iv =>
      SnapshotSourceAction.emitDef _ none (.indexChecked vw iv (some origin)) (by intros; intro h; cases h)).snapshots

theorem snapshot_source_dereference {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : SnapshotSourceExpression env results expr) : SnapshotSourcePlace env results (.deref expr) := by
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
        exact ((SnapshotSourceAction.emitDef _ none (.slotAddr index) (by intros; intro h; cases h)).bind fun value =>
          (SnapshotSourceAction.emitDef _ none (.load value) (by intros; intro h; cases h)).bind fun loaded =>
            (SnapshotSourceAction.recordReadValueRootRecipe _ none loaded (.var index)).bind fun _ =>
              SnapshotSourceAction.pure _ none loaded).snapshots
      | _ => simp [Core.sliceRefTy] at special
    | _ => simp [Core.sliceRefTy] at special

theorem snapshot_source_view_of {env : Core.TEnv} {results : List Ty} (place : Place)
    (child : SnapshotSourcePlace env results place) : SnapshotSourceView env results (.of place) := by
  intro element writable start finish source before result after generated frames run
  obtain ⟨info, childFinish, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  let lowered := lowerPlace place (lowerEnv env.mod env.vars results) before
  exact SnapshotSourceTrace.lowerView_of childSource generated (show lowerPlace place _ before = lowered from rfl)
    (child childSource before lowered.1 lowered.2 generated trivial rfl) (Nat.le_refl _) run

theorem snapshot_source_view_val {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : SnapshotSourceExpression env results expr) : SnapshotSourceView env results (.val expr) := by
  intro element writable start finish source
  obtain ⟨type, childFinish, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  exact ((SnapshotSourceAction.lowerExpr expr (child childSource)).bind fun value =>
    SnapshotSourceAction.emitDef _ none (.sliceView value) (by intros; intro h; cases h)).snapshots

theorem snapshot_source_length {env : Core.TEnv} {results : List Ty} (view : View)
    (child : SnapshotSourceView env results view) : SnapshotSourceExpression env results (.len view) := by
  intro type start finish source
  obtain ⟨pair, childFinish, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact ((SnapshotSourceAction.lowerView view (child childSource)).bind fun value =>
    SnapshotSourceAction.emitDef _ none (.viewLen value) (by intros; intro h; cases h)).snapshots


theorem snapshot_source_eachSource {env : Core.TEnv} {results : List Ty} (view : View)
    (child : SnapshotSourceView env results view) {element : Ty} {writable : Bool} {start finish : Nat}
    (source : Core.tyView env view start = .ok ((element, writable), finish)) :
    SnapshotTraceRun (lowerEnv env.mod env.vars results) none (lowerEachSource view) := by
  intro before result after generated frames run
  have sameState : (lowerEachSource view (lowerEnv env.mod env.vars results) before).2 =
      (lowerView view (lowerEnv env.mod env.vars results) before).2 := by
    cases view <;> rfl
  have equal : (lowerView view (lowerEnv env.mod env.vars results) before).2 = after :=
    sameState.symm.trans (congrArg Prod.snd run)
  have trace := child source before (lowerView view (lowerEnv env.mod env.vars results) before).1
    (lowerView view (lowerEnv env.mod env.vars results) before).2 generated trivial rfl
  rw [equal] at trace
  exact trace

theorem SnapshotSourceAction.lowerEachSource {le : LEnv} (view : View)
    (source : SnapshotTraceRun le none (lowerEachSource view)) :
    SnapshotSourceAction le none (lowerEachSource view) :=
  ⟨source, dense_lowerEachSource view, advB_lowerEachSource view, generatedTargets_lowerEachSource none view,
    types_lowerEachSource view, generatedTargetFrame_lowerEachSource none view⟩

end Goose.Lower.Validation

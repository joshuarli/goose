import Goose.Lower.Validation.EmittedMetadataStaticProfileSourceCollections
import Goose.Lower.Validation.SourceStatementTypingStorage

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem profile_source_let {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (slot : SlotId) (expr : Expr) (origin : OriginId)
    (child : EmittedProfileSourceExpression env results expr) : EmittedProfileSourceStatement env results scope (.letS slot expr origin) := by
  intro output start finish source loop
  obtain ⟨localVar, type, childStart, declared, childSource, passable, _⟩ := tyStmt_let_children source
  exact (((child childSource)).bind fun value =>
    (EmittedProfileRun.coerceSlot slot value origin).bind fun value =>
      EmittedProfileRun.emitEffect (.slotInit slot value (some origin)) trivial)

theorem profile_source_rebind {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (slot : SlotId) (expr : Expr) (origin : OriginId)
    (child : EmittedProfileSourceExpression env results expr) : EmittedProfileSourceStatement env results scope (.rebind slot expr origin) := by
  intro output start finish source loop
  obtain ⟨localVar, type, localRow, _, _, _, childSource, _, _⟩ := tyStmt_rebind_children source
  exact (((child childSource)).bind fun value =>
    (EmittedProfileRun.coerceSlot slot value origin).bind fun value =>
      (EmittedProfileRun.emitDef (.slotAddr slot) (by intro; trivial)).bind fun address =>
        EmittedProfileRun.emitEffect (.store address value (some origin)) trivial)

theorem profile_source_assign {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : EmittedProfileSourcePlace env results place) (exprChild : EmittedProfileSourceExpression env results expr) : EmittedProfileSourceStatement env results scope (.assign place expr origin) := by
  intro output start finish source loop
  obtain ⟨info, childStart, placeSource, exprSource, _, _, _⟩ := tyStmt_assign_children source
  exact (((placeChild placeSource)).bind fun address =>
    ((exprChild exprSource)).bind fun value =>
      EmittedProfileRun.emitEffect (.store address value (some origin)) trivial)

theorem profile_source_assignOp {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (op : BinOp) (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : EmittedProfileSourcePlace env results place) (exprChild : EmittedProfileSourceExpression env results expr) : EmittedProfileSourceStatement env results scope (.assignOp op place expr origin) := by
  intro output start finish source loop
  obtain ⟨info, integer, childStart, placeSource, infoType, exprSource, _, _⟩ := tyStmt_assignOp_children source
  exact (((placeChild placeSource)).bind fun address =>
    (EmittedProfileRun.emitDef (.load address) (by intro; trivial)).bind fun old =>
      ((exprChild exprSource)).bind fun rhs =>
        (EmittedProfileRun.intTyOf old).bind fun type =>
          (EmittedProfileRun.emitDef (.bin op type old rhs (some origin)) (by intro; trivial)).bind fun value =>
            EmittedProfileRun.emitEffect (.store address value (some origin)) trivial)

theorem profile_source_clear {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (origin : OriginId)
    (child : EmittedProfileSourcePlace env results place) : EmittedProfileSourceStatement env results scope (.clear place origin) := by
  intro output start finish source loop
  have profile := static_tyStmt_clear_profile source
  obtain ⟨info, element, childSource, _, _, _⟩ := tyStmt_clear_children source
  exact (((child childSource)).bind fun address =>
    EmittedProfileRun.emitEffect (.clear address (some origin)) profile)

theorem profile_source_append {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (view : View) (origin : OriginId)
    (placeChild : EmittedProfileSourcePlace env results place) (viewChild : EmittedProfileSourceView env results view) : EmittedProfileSourceStatement env results scope (.append place view origin) := by
  intro output start finish source loop
  obtain ⟨info, element, writable, childStart, placeSource, _, viewSource, _, _⟩ := tyStmt_append_children source
  exact (((placeChild placeSource)).bind fun address =>
    ((viewChild viewSource)).bind fun value =>
      EmittedProfileRun.emitEffect (.append address value (some origin)) trivial)

theorem profile_source_popN {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : EmittedProfileSourcePlace env results place) (exprChild : EmittedProfileSourceExpression env results expr) : EmittedProfileSourceStatement env results scope (.popN place expr origin) := by
  intro output start finish source loop
  have profile := static_tyStmt_popN_profile source
  obtain ⟨info, element, integer, childStart, placeSource, _, exprSource, _, _⟩ := tyStmt_popN_children source
  exact (((placeChild placeSource)).bind fun address =>
    ((exprChild exprSource)).bind fun value =>
      EmittedProfileRun.emitEffect (.popN address value (some origin)) profile)

theorem profile_source_assignWhole {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : EmittedProfileSourcePlace env results place) (exprChild : EmittedProfileSourceExpression env results expr) : EmittedProfileSourceStatement env results scope (.assignWhole place expr origin) := by
  intro output start finish source loop
  have profile := static_tyStmt_assignWhole_profile source
  obtain ⟨info, element, childStart, placeSource, _, exprSource, _, _, _⟩ := tyStmt_assignWhole_children source
  exact (((placeChild placeSource)).bind fun address =>
    (EmittedProfileRun.emitEffect (.clear address (some origin)) profile).bind fun _ =>
      ((exprChild exprSource)).bind fun value =>
        EmittedProfileRun.emitEffect (.replace address value (some origin)) profile)

theorem profile_source_resize {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (size : Expr) (fill : Option Expr) (origin : OriginId)
    (placeChild : EmittedProfileSourcePlace env results place) (sizeChild : EmittedProfileSourceExpression env results size)
    (fillChild : ∀ expr, fill = some expr → EmittedProfileSourceExpression env results expr) :
    EmittedProfileSourceStatement env results scope (.resize place size fill origin) := by
  intro output start finish source loop
  have profile := static_tyStmt_resize_profile source
  obtain ⟨info, element, integer, childStart, sizeFinish, placeSource, _, sizeSource, fillSource, _, _⟩ :=
    tyStmt_resize_children source
  cases fill with
  | none =>
    exact (((placeChild placeSource)).bind fun address =>
      ((sizeChild sizeSource)).bind fun count =>
        (EmittedProfileRun.pure none).bind fun value =>
          EmittedProfileRun.emitEffect (.resize address count value (some origin)) profile)
  | some expr =>
    exact (((placeChild placeSource)).bind fun address =>
      ((sizeChild sizeSource)).bind fun count =>
        (((fillChild expr rfl fillSource)).bind
          (fun value => EmittedProfileRun.pure (some value))).bind fun value =>
            EmittedProfileRun.emitEffect (.resize address count value (some origin)) profile)

end Goose.Lower.Validation

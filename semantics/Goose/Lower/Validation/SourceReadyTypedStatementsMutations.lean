import Goose.Lower.Validation.SourceReadyTypedStatementsNative

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before : LS}
  {typingEnv output : TEnv} {results : List Ty} {loop : Option LoopCtx}
  {scope start finish : Nat} {origin : OriginId}

theorem typed_ready_assign {place : Place} {expression : Expr}
    (source : Core.tyStmt typingEnv scope (.assign place expression origin) start = .ok (output, finish))
    (visible : VisibleSlotsReady typingEnv state)
    (placeChild : ∀ info next, Core.tyPlace typingEnv place start = .ok (info, next) →
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before)
    (valueChild : ∀ type next, Core.tyExpr typingEnv expression next = .ok (type, finish) →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results)
        (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.assign place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.assign place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  obtain ⟨info, next, placeSource, valueSource, _, _, rfl⟩ := tyStmt_assign_children source
  exact ⟨ready_assign (loop := loop) rfl rfl rfl (placeChild info next placeSource) (valueChild info.ty next valueSource), fun _ => visible⟩

theorem typed_ready_assignWhole {place : Place} {expression : Expr}
    (source : Core.tyStmt typingEnv scope (.assignWhole place expression origin) start = .ok (output, finish))
    (visible : VisibleSlotsReady typingEnv state)
    (placeChild : ∀ info next, Core.tyPlace typingEnv place start = .ok (info, next) →
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before)
    (valueChild : ∀ type next, Core.tyExpr typingEnv expression next = .ok (type, finish) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let address := lowerPlace place env before
      ValueReadyAt state (lowerExpr expression) env (emitEffect (.clear address.1 (some origin)) env address.2).2) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.assignWhole place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.assignWhole place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  obtain ⟨info, element, next, placeSource, _, valueSource, _, _, rfl⟩ := tyStmt_assignWhole_children source
  exact ⟨ready_assignWhole (loop := loop) rfl rfl rfl rfl (placeChild info next placeSource)
    (valueChild info.ty next valueSource), fun _ => visible⟩

theorem typed_ready_clear {place : Place}
    (source : Core.tyStmt typingEnv scope (.clear place origin) start = .ok (output, finish))
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ info, Core.tyPlace typingEnv place start = .ok (info, finish) →
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.clear place origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.clear place origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  obtain ⟨info, element, checked, _, _, rfl⟩ := tyStmt_clear_children source
  exact ⟨ready_clear (loop := loop) (child info checked), fun _ => visible⟩

theorem typed_ready_append {place : Place} {view : View}
    (source : Core.tyStmt typingEnv scope (.append place view origin) start = .ok (output, finish))
    (visible : VisibleSlotsReady typingEnv state)
    (placeChild : ∀ info next, Core.tyPlace typingEnv place start = .ok (info, next) →
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before)
    (viewChild : ∀ element writable next, Core.tyView typingEnv view next = .ok ((element, writable), finish) →
      ValueReadyAt state (lowerView view) (lowerEnv typingEnv.mod typingEnv.vars results)
        (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.append place view origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.append place view origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  obtain ⟨info, element, writable, next, placeSource, _, viewSource, _, rfl⟩ := tyStmt_append_children source
  exact ⟨ready_append (loop := loop) (placeChild info next placeSource) (viewChild element writable next viewSource), fun _ => visible⟩

theorem typed_ready_popN {place : Place} {count : Expr}
    (source : Core.tyStmt typingEnv scope (.popN place count origin) start = .ok (output, finish))
    (visible : VisibleSlotsReady typingEnv state)
    (placeChild : ∀ info next, Core.tyPlace typingEnv place start = .ok (info, next) →
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before)
    (countChild : ∀ integer next, Core.tyExpr typingEnv count next = .ok (.int integer, finish) →
      ValueReadyAt state (lowerExpr count) (lowerEnv typingEnv.mod typingEnv.vars results)
        (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.popN place count origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.popN place count origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  obtain ⟨info, element, integer, next, placeSource, _, countSource, _, rfl⟩ := tyStmt_popN_children source
  exact ⟨ready_popN (loop := loop) (placeChild info next placeSource) (countChild integer next countSource), fun _ => visible⟩

theorem typed_ready_resize {place : Place} {size : Expr} {fill : Option Expr}
    (source : Core.tyStmt typingEnv scope (.resize place size fill origin) start = .ok (output, finish))
    (visible : VisibleSlotsReady typingEnv state)
    (placeChild : ∀ info next, Core.tyPlace typingEnv place start = .ok (info, next) →
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before)
    (sizeChild : ∀ integer next last, Core.tyExpr typingEnv size next = .ok (.int integer, last) →
      ValueReadyAt state (lowerExpr size) (lowerEnv typingEnv.mod typingEnv.vars results)
        (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (fillChild : ∀ expression type next, fill = some expression → Core.tyExpr typingEnv expression next = .ok (type, finish) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      ValueReadyAt state (lowerExpr expression) env (lowerExpr size env (lowerPlace place env before).2).2) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.resize place size fill origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.resize place size fill origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  obtain ⟨info, element, integer, next, last, placeSource, _, sizeSource, fillSource, _, rfl⟩ := tyStmt_resize_children source
  have placeReady := placeChild info next placeSource
  have sizeReady := sizeChild integer next last sizeSource
  cases fill with
  | none => exact ⟨ready_resize_none (loop := loop) placeReady sizeReady, fun _ => visible⟩
  | some expression => exact ⟨ready_resize_some (loop := loop) placeReady sizeReady (fillChild expression element last rfl fillSource), fun _ => visible⟩

end Goose.Lower.Validation.ReplacementContentFlowSource

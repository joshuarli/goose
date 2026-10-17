import Goose.Lower.Validation.SourceReadyTypedStatementsFrames
import Goose.Lower.Validation.SourceReadyObservationOutput

namespace Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyStatementObservations

open Goose.Core Goose.GIR SummaryPreservation
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

private theorem child_frames {types : Array (Option VTy)} {child final completed : LS}
    (native : NativeRows types final) (extension : final.Ext completed)
    (allocated : final.vals.size ≤ completed.vals.size)
    (typedPrefix : TypePrefix child final) (advance : child.Adv final) :
    NativeRows types child ∧ child.Ext completed ∧ child.vals.size ≤ completed.vals.size :=
  ⟨native.of_prefix typedPrefix, advance.ext.trans extension, Nat.le_trans advance.vals allocated⟩

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before : LS}
  {typingEnv output : TEnv} {results : List Ty} {loop : Option LoopCtx}
  {scope start finish : Nat} {origin : OriginId}

theorem letS {slot : SlotId} {expression : Expr}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyStmt typingEnv scope (.letS slot expression origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (slotCount : func.slots.size = typingEnv.vars.size)
    (native : NativeRows types (lowerStmt loop (.letS slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.letS slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.letS slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ type next, Core.tyExpr typingEnv expression next = .ok (type, finish) →
      let prior := before
      GeneratedBuilderState prior → NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior).2) :
    (EmitsOnly (ReadyOperands state) before (lowerStmt loop (.letS slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.letS slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerStmt loop (.letS slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let value := lowerExpr expression env before
  obtain ⟨localVar, type, next, declared, checked, _, outputEq⟩ := tyStmt_let_children source
  have child0 := by
    have tailTypes := TypeRun.bind (types_coerceSlot slot value.1 origin) fun converted => types_emitEffect (.slotInit slot converted (some origin))
    have tailAdvance := AdvB.bind (advB_coerceSlot slot value.1 origin) fun converted => advB_emitEffect (.slotInit slot converted (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact child type next checked (generated) childNative childExtension childAllocated visible
  exact ⟨SourceReadyStatementFrames.letS (loop := loop) frame source generated slotCount native extension allocated visible (by intros; exact child0.1),
    ReadyCallObservations.statement_let slot expression origin child0.2⟩

theorem rebind {slot : SlotId} {expression : Expr}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyStmt typingEnv scope (.rebind slot expression origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (native : NativeRows types (lowerStmt loop (.rebind slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.rebind slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.rebind slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ type, Core.tyExpr typingEnv expression start = .ok (type, finish) →
      let prior := before
      GeneratedBuilderState prior → NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior).2) :
    (EmitsOnly (ReadyOperands state) before (lowerStmt loop (.rebind slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.rebind slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerStmt loop (.rebind slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let value := lowerExpr expression env before
  obtain ⟨localVar, type, _, _, _, _, checked, _, outputEq⟩ := tyStmt_rebind_children source
  have child0 := by
    have tailTypes := TypeRun.bind (types_coerceSlot slot value.1 origin) fun converted => TypeRun.bind (types_emitDef (.slotAddr slot)) fun address => types_emitEffect (.store address converted (some origin))
    have tailAdvance := AdvB.bind (advB_coerceSlot slot value.1 origin) fun converted => AdvB.bind (advB_emitDef (.slotAddr slot)) fun address => advB_emitEffect (.store address converted (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact child type checked (generated) childNative childExtension childAllocated visible
  exact ⟨SourceReadyStatementFrames.rebind (loop := loop) frame source generated native extension allocated visible (by intros; exact child0.1),
    ReadyCallObservations.statement_rebind slot expression origin child0.2⟩

theorem expression {expression : Expr}
    (source : Core.tyStmt typingEnv scope (.expr expression origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (native : NativeRows types (lowerStmt loop (.expr expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.expr expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.expr expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ type, Core.tyExpr typingEnv expression start = .ok (type, finish) →
      let prior := before
      GeneratedBuilderState prior → NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior).2) :
    (EmitsOnly (ReadyOperands state) before (lowerStmt loop (.expr expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.expr expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerStmt loop (.expr expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let value := lowerExpr expression env before
  obtain ⟨type, checked, outputEq⟩ := tyStmt_expr_children source
  have child0 := by
    have tailTypes := TypeRun.pure ()
    have tailAdvance := AdvB.pure ()
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact child type checked (generated) childNative childExtension childAllocated visible
  exact ⟨SourceReadyStatementFrames.expression (loop := loop) source generated native extension allocated visible (by intros; exact child0.1),
    ReadyCallObservations.statement_expression expression origin child0.2⟩

theorem assertS {expression : Expr}
    (source : Core.tyStmt typingEnv scope (.assertS expression origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (native : NativeRows types (lowerStmt loop (.assertS expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.assertS expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.assertS expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child :  Core.tyExpr typingEnv expression start = .ok (.bool, finish) →
      let prior := before
      GeneratedBuilderState prior → NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior).2) :
    (EmitsOnly (ReadyOperands state) before (lowerStmt loop (.assertS expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.assertS expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerStmt loop (.assertS expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let value := lowerExpr expression env before
  obtain ⟨checked, outputEq⟩ := tyStmt_assert_children source
  have child0 := by
    have tailTypes := types_assert_core value.1 origin
    have tailAdvance := advB_assert_core value.1 origin
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact child checked (generated) childNative childExtension childAllocated visible
  exact ⟨SourceReadyStatementFrames.assertS (loop := loop) source generated native extension allocated visible (by intros; exact child0.1),
    ReadyCallObservations.statement_assert expression origin child0.2⟩

theorem exit {expression : Expr}
    (source : Core.tyStmt typingEnv scope (.exit expression origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (native : NativeRows types (lowerStmt loop (.exit expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.exit expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.exit expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ integer, Core.tyExpr typingEnv expression start = .ok (.int integer, finish) →
      let prior := before
      GeneratedBuilderState prior → NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior).2) :
    (EmitsOnly (ReadyOperands state) before (lowerStmt loop (.exit expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.exit expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerStmt loop (.exit expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let value := lowerExpr expression env before
  obtain ⟨integer, checked, outputEq⟩ := tyStmt_exit_children source
  have child0 := by
    have tailTypes := types_emitTerm (.exit value.1 (some origin))
    have tailAdvance := advB_emitTerm (.exit value.1 (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact child integer checked (generated) childNative childExtension childAllocated visible
  exact ⟨SourceReadyStatementFrames.exit (loop := loop) source generated native extension allocated visible (by intros; exact child0.1),
    ReadyCallObservations.statement_exit expression origin child0.2⟩

theorem returnSome {expression : Expr}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyStmt typingEnv scope (.ret (some expression) origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (native : NativeRows types (lowerStmt loop (.ret (some expression) origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.ret (some expression) origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.ret (some expression) origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ type, Core.tyExpr typingEnv expression start = .ok (type, finish) →
      let prior := before
      GeneratedBuilderState prior → NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior).2) :
    (EmitsOnly (ReadyOperands state) before (lowerStmt loop (.ret (some expression) origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.ret (some expression) origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerStmt loop (.ret (some expression) origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let value := lowerExpr expression env before
  obtain ⟨expected, actual, impl, _, _, _, checked, _, outputEq⟩ := tyStmt_return_children source
  have child0 := by
    have tailTypes := TypeRun.bind (types_coerceResult value.1 origin) fun converted => TypeRun.bind (types_leaveTo 0) fun _ => types_emitTerm (.ret [converted] (some origin))
    have tailAdvance := AdvB.bind (advB_coerceResult value.1 origin) fun converted => AdvB.bind (advB_leaveTo 0) fun _ => advB_emitTerm (.ret [converted] (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact child actual checked (generated) childNative childExtension childAllocated visible
  exact ⟨SourceReadyStatementFrames.returnSome (loop := loop) frame source generated native extension allocated visible (by intros; exact child0.1),
    ReadyCallObservations.statement_return_some expression origin child0.2⟩

theorem assign {place : Place} {expression : Expr}
    (source : Core.tyStmt typingEnv scope (.assign place expression origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (native : NativeRows types (lowerStmt loop (.assign place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.assign place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.assign place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (placeChild : ∀ info next, Core.tyPlace typingEnv place start = .ok (info, next) →
      let prior := before
      GeneratedBuilderState prior → NativeRows types (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior).2)
    (valueChild : ∀ type next, Core.tyExpr typingEnv expression next = .ok (type, finish) →
      let prior := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2
      GeneratedBuilderState prior → NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior).2) :
    (EmitsOnly (ReadyOperands state) before (lowerStmt loop (.assign place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.assign place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerStmt loop (.assign place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  let value := lowerExpr expression env address.2
  obtain ⟨info, next, placeSource, valueSource, _, _, outputEq⟩ := tyStmt_assign_children source
  have child0 := by
    have tailTypes := TypeRun.bind (types_lowerExpr expression) fun v => types_emitEffect (.store address.1 v (some origin))
    have tailAdvance := AdvB.bind (advB_lowerExpr expression) fun v => advB_emitEffect (.store address.1 v (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact placeChild info next placeSource (generated) childNative childExtension childAllocated visible
  have child1 := by
    have tailTypes := types_emitEffect (.store address.1 value.1 (some origin))
    have tailAdvance := advB_emitEffect (.store address.1 value.1 (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2 _ _ rfl)
    exact valueChild info.ty next valueSource (generated.lowerPlace place rfl) childNative childExtension childAllocated visible
  exact ⟨SourceReadyStatementFrames.assign (loop := loop) source generated native extension allocated visible (by intros; exact child0.1) (by intros; exact child1.1),
    ReadyCallObservations.statement_assign place expression origin child0.2 child1.2⟩

theorem popN {place : Place} {expression : Expr}
    (source : Core.tyStmt typingEnv scope (.popN place expression origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (native : NativeRows types (lowerStmt loop (.popN place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.popN place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.popN place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (placeChild : ∀ info next, Core.tyPlace typingEnv place start = .ok (info, next) →
      let prior := before
      GeneratedBuilderState prior → NativeRows types (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior).2)
    (valueChild : ∀ integer next, Core.tyExpr typingEnv expression next = .ok (.int integer, finish) →
      let prior := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2
      GeneratedBuilderState prior → NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior).2) :
    (EmitsOnly (ReadyOperands state) before (lowerStmt loop (.popN place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.popN place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerStmt loop (.popN place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  let value := lowerExpr expression env address.2
  obtain ⟨info, element, integer, next, placeSource, _, countSource, _, outputEq⟩ := tyStmt_popN_children source
  have child0 := by
    have tailTypes := TypeRun.bind (types_lowerExpr expression) fun v => types_emitEffect (.popN address.1 v (some origin))
    have tailAdvance := AdvB.bind (advB_lowerExpr expression) fun v => advB_emitEffect (.popN address.1 v (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact placeChild info next placeSource (generated) childNative childExtension childAllocated visible
  have child1 := by
    have tailTypes := types_emitEffect (.popN address.1 value.1 (some origin))
    have tailAdvance := advB_emitEffect (.popN address.1 value.1 (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2 _ _ rfl)
    exact valueChild integer next countSource (generated.lowerPlace place rfl) childNative childExtension childAllocated visible
  exact ⟨SourceReadyStatementFrames.popN (loop := loop) source generated native extension allocated visible (by intros; exact child0.1) (by intros; exact child1.1),
    ReadyCallObservations.mutation_popN place expression origin child0.2 child1.2⟩

theorem append {place : Place} {view : View}
    (source : Core.tyStmt typingEnv scope (.append place view origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (native : NativeRows types (lowerStmt loop (.append place view origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.append place view origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.append place view origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (placeChild : ∀ info next, Core.tyPlace typingEnv place start = .ok (info, next) →
      let prior := before
      GeneratedBuilderState prior → NativeRows types (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior).2)
    (viewChild : ∀ element writable next, Core.tyView typingEnv view next = .ok ((element, writable), finish) →
      let prior := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2
      GeneratedBuilderState prior → NativeRows types (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerView view) (lowerEnv typingEnv.mod typingEnv.vars results) prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerView view) (lowerEnv typingEnv.mod typingEnv.vars results) prior).2) :
    (EmitsOnly (ReadyOperands state) before (lowerStmt loop (.append place view origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.append place view origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerStmt loop (.append place view origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  let value := lowerView view env address.2
  obtain ⟨info, element, writable, next, placeSource, _, viewSource, _, outputEq⟩ := tyStmt_append_children source
  have child0 := by
    have tailTypes := TypeRun.bind (types_lowerView view) fun v => types_emitEffect (.append address.1 v (some origin))
    have tailAdvance := AdvB.bind (advB_lowerView view) fun v => advB_emitEffect (.append address.1 v (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact placeChild info next placeSource (generated) childNative childExtension childAllocated visible
  have child1 := by
    have tailTypes := types_emitEffect (.append address.1 value.1 (some origin))
    have tailAdvance := advB_emitEffect (.append address.1 value.1 (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2) native extension allocated
      (by exact tailTypes env (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2 _ _ rfl)
      (by exact tailAdvance env (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2 _ _ rfl)
    exact viewChild element writable next viewSource (generated.lowerPlace place rfl) childNative childExtension childAllocated visible
  exact ⟨SourceReadyStatementFrames.append (loop := loop) source generated native extension allocated visible (by intros; exact child0.1) (by intros; exact child1.1),
    ReadyCallObservations.mutation_append place view origin child0.2 child1.2⟩

theorem clear {place : Place}
    (source : Core.tyStmt typingEnv scope (.clear place origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (native : NativeRows types (lowerStmt loop (.clear place origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.clear place origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.clear place origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ info, Core.tyPlace typingEnv place start = .ok (info, finish) →
      let prior := before
      GeneratedBuilderState prior → NativeRows types (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior).2) :
    (EmitsOnly (ReadyOperands state) before (lowerStmt loop (.clear place origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.clear place origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerStmt loop (.clear place origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  obtain ⟨info, element, checked, _, _, outputEq⟩ := tyStmt_clear_children source
  have child0 := by
    have tailTypes := types_emitEffect (.clear address.1 (some origin))
    have tailAdvance := advB_emitEffect (.clear address.1 (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact child info checked (generated) childNative childExtension childAllocated visible
  exact ⟨SourceReadyStatementFrames.clear (loop := loop) source generated native extension allocated visible (by intros; exact child0.1),
    ReadyCallObservations.mutation_clear place origin child0.2⟩

theorem assignWhole {place : Place} {expression : Expr}
    (source : Core.tyStmt typingEnv scope (.assignWhole place expression origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (native : NativeRows types (lowerStmt loop (.assignWhole place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.assignWhole place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.assignWhole place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (placeChild : ∀ info next, Core.tyPlace typingEnv place start = .ok (info, next) →
      let prior := before
      GeneratedBuilderState prior → NativeRows types (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior).2)
    (valueChild : ∀ type next, Core.tyExpr typingEnv expression next = .ok (type, finish) →
      let prior := (emitEffect (.clear (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).1 (some origin)) (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2
      GeneratedBuilderState prior → NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior).2) :
    (EmitsOnly (ReadyOperands state) before (lowerStmt loop (.assignWhole place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.assignWhole place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerStmt loop (.assignWhole place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  let cleared := (emitEffect (.clear address.1 (some origin)) env address.2).2
  let value := lowerExpr expression env cleared
  obtain ⟨info, element, next, placeSource, _, valueSource, _, _, outputEq⟩ := tyStmt_assignWhole_children source
  have child0 := by
    have tailTypes := TypeRun.bind (types_emitEffect (.clear address.1 (some origin))) fun _ => TypeRun.bind (types_lowerExpr expression) fun v => types_emitEffect (.replace address.1 v (some origin))
    have tailAdvance := AdvB.bind (advB_emitEffect (.clear address.1 (some origin))) fun _ => AdvB.bind (advB_lowerExpr expression) fun v => advB_emitEffect (.replace address.1 v (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact placeChild info next placeSource (generated) childNative childExtension childAllocated visible
  have child1 := by
    have tailTypes := types_emitEffect (.replace address.1 value.1 (some origin))
    have tailAdvance := advB_emitEffect (.replace address.1 value.1 (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (emitEffect (.clear (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).1 (some origin)) (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (emitEffect (.clear (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).1 (some origin)) (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (emitEffect (.clear (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).1 (some origin)) (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2).2 _ _ rfl)
    exact valueChild info.ty next valueSource ((generated.lowerPlace place rfl).emitEffect _ rfl) childNative childExtension childAllocated visible
  exact ⟨SourceReadyStatementFrames.assignWhole (loop := loop) source generated native extension allocated visible (by intros; exact child0.1) (by intros; exact child1.1),
    ReadyCallObservations.mutation_assignWhole place expression origin child0.2 child1.2⟩

theorem assignOp {place : Place} {expression : Expr} {operation : BinOp}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyStmt typingEnv scope (.assignOp operation place expression origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (native : NativeRows types (lowerStmt loop (.assignOp operation place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.assignOp operation place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.assignOp operation place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (placeChild : ∀ info next, Core.tyPlace typingEnv place start = .ok (info, next) →
      let prior := before
      GeneratedBuilderState prior → NativeRows types (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior).2)
    (valueChild : ∀ integer next, Core.tyExpr typingEnv expression next = .ok (.int integer, finish) →
      let prior := (Lower.emitDef (.load (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).1) (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2
      GeneratedBuilderState prior → NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior).2) :
    (EmitsOnly (ReadyOperands state) before (lowerStmt loop (.assignOp operation place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.assignOp operation place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerStmt loop (.assignOp operation place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  let loaded := Lower.emitDef (.load address.1) env address.2
  let value := lowerExpr expression env loaded.2
  obtain ⟨info, integer, next, placeSource, _, valueSource, _, outputEq⟩ := tyStmt_assignOp_children source
  have child0 := by
    have tailTypes := TypeRun.bind (types_emitDef (.load address.1)) fun old => TypeRun.bind (types_lowerExpr expression) fun rhs => TypeRun.bind (types_intTyOf old) fun t => TypeRun.bind (types_emitDef (.bin operation t old rhs (some origin))) fun v => types_emitEffect (.store address.1 v (some origin))
    have tailAdvance := AdvB.bind (advB_emitDef (.load address.1)) fun old => AdvB.bind (advB_lowerExpr expression) fun rhs => AdvB.bind (advB_intTyOf old) fun t => AdvB.bind (advB_emitDef (.bin operation t old rhs (some origin))) fun v => advB_emitEffect (.store address.1 v (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact placeChild info next placeSource (generated) childNative childExtension childAllocated visible
  have child1 := by
    have tailTypes := TypeRun.bind (types_intTyOf loaded.1) fun t => TypeRun.bind (types_emitDef (.bin operation t loaded.1 value.1 (some origin))) fun v => types_emitEffect (.store address.1 v (some origin))
    have tailAdvance := AdvB.bind (advB_intTyOf loaded.1) fun t => AdvB.bind (advB_emitDef (.bin operation t loaded.1 value.1 (some origin))) fun v => advB_emitEffect (.store address.1 v (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (Lower.emitDef (.load (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).1) (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (Lower.emitDef (.load (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).1) (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (Lower.emitDef (.load (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).1) (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2).2 _ _ rfl)
    exact valueChild integer next valueSource ((generated.lowerPlace place rfl).emitDef _ rfl) childNative childExtension childAllocated visible
  exact ⟨SourceReadyStatementFrames.assignOp (loop := loop) frame source generated native extension allocated visible (by intros; exact child0.1) (by intros; exact child1.1),
    ReadyCallObservations.statement_assignOp operation place expression origin child0.2 child1.2⟩

theorem resize {place : Place} {size : Expr} {fill : Option Expr}
    (source : Core.tyStmt typingEnv scope (.resize place size fill origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (native : NativeRows types (lowerStmt loop (.resize place size fill origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.resize place size fill origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.resize place size fill origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (placeChild : ∀ info next, Core.tyPlace typingEnv place start = .ok (info, next) →
      GeneratedBuilderState before →
      NativeRows types (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before
        ((lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (sizeChild : ∀ integer next last, Core.tyExpr typingEnv size next = .ok (.int integer, last) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let prior := (lowerPlace place env before).2
      GeneratedBuilderState prior → NativeRows types (lowerExpr size env prior).2 →
      (lowerExpr size env prior).2.Ext completed →
      (lowerExpr size env prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr size) env prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerExpr size) env prior).2)
    (fillChild : ∀ expression type next, fill = some expression →
      Core.tyExpr typingEnv expression next = .ok (type, finish) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let prior := (lowerExpr size env (lowerPlace place env before).2).2
      GeneratedBuilderState prior → NativeRows types (lowerExpr expression env prior).2 →
      (lowerExpr expression env prior).2.Ext completed →
      (lowerExpr expression env prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) env prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerExpr expression) env prior).2) :
    (EmitsOnly (ReadyOperands state) before (lowerStmt loop (.resize place size fill origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.resize place size fill origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerStmt loop (.resize place size fill origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  let sized := lowerExpr size env address.2
  let filling : B (Option ValueId) := match fill with
    | none => pure none
    | some expression => do pure (some (← lowerExpr expression))
  have fillingTypes : TypeRun filling := by
    cases fill with
    | none => exact TypeRun.pure none
    | some expression => exact TypeRun.bind (types_lowerExpr expression) fun v => TypeRun.pure (some v)
  have fillingAdvance : AdvB filling := by
    cases fill with
    | none => exact AdvB.pure none
    | some expression => exact AdvB.bind (advB_lowerExpr expression) fun v => AdvB.pure (some v)
  obtain ⟨info, element, integer, next, last, placeSource, _, sizeSource, fillSource, _, outputEq⟩ :=
    tyStmt_resize_children source
  have child0 := by
    have tailTypes := TypeRun.bind (types_lowerExpr size) fun n => TypeRun.bind fillingTypes fun f =>
      types_emitEffect (.resize address.1 n f (some origin))
    have tailAdvance := AdvB.bind (advB_lowerExpr size) fun n => AdvB.bind fillingAdvance fun f =>
      advB_emitEffect (.resize address.1 n f (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames (child := address.2) native extension allocated
      (by cases fill <;> exact tailTypes env address.2 _ _ rfl)
      (by cases fill <;> exact tailAdvance env address.2 _ _ rfl)
    exact placeChild info next placeSource generated childNative childExtension childAllocated visible
  have child1 := by
    have tailTypes := TypeRun.bind fillingTypes fun f => types_emitEffect (.resize address.1 sized.1 f (some origin))
    have tailAdvance := AdvB.bind fillingAdvance fun f => advB_emitEffect (.resize address.1 sized.1 f (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames (child := sized.2) native extension allocated
      (by cases fill <;> exact tailTypes env sized.2 _ _ rfl)
      (by cases fill <;> exact tailAdvance env sized.2 _ _ rfl)
    exact sizeChild integer next last sizeSource (generated.lowerPlace place rfl)
      childNative childExtension childAllocated visible
  cases fill with
  | none =>
    exact ⟨SourceReadyStatementFrames.resize (loop := loop) source generated native extension allocated visible
      (by intros; exact child0.1) (by intros; exact child1.1)
      (by intro expression type next impossible; cases impossible),
      ReadyCallObservations.mutation_resize_none place size origin child0.2 child1.2⟩
  | some expression =>
    let value := lowerExpr expression env sized.2
    have child2 := by
      obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames (child := value.2) native extension allocated
        (by exact types_emitEffect (.resize address.1 sized.1 (some value.1) (some origin)) env value.2 _ _ rfl)
        (by exact advB_emitEffect (.resize address.1 sized.1 (some value.1) (some origin)) env value.2 _ _ rfl)
      exact fillChild expression element last rfl fillSource ((generated.lowerPlace place rfl).lowerExpr size rfl)
        childNative childExtension childAllocated visible
    exact ⟨SourceReadyStatementFrames.resize (loop := loop) source generated native extension allocated visible
      (by intros; exact child0.1) (by intros; exact child1.1)
      (by
        intro selected type next same
        cases same
        intros
        exact child2.1),
      ReadyCallObservations.mutation_resize_some place size expression origin child0.2 child1.2 child2.2⟩

private theorem lower_print_args_append_run (earlier later : List PrintArg) (env : LEnv) (before : LS) :
    lowerPrintArgs (earlier ++ later) env before =
      let first := lowerPrintArgs earlier env before
      let last := lowerPrintArgs later env first.2
      (first.1 ++ last.1, last.2) := by
  induction earlier generalizing before with
  | nil => simp only [List.nil_append, lowerPrintArgs, pure_run, List.nil_append]
  | cons argument rest ih =>
    cases argument with
    | text text =>
      simpa only [List.cons_append, lowerPrintArgs, bind_run, pure_run] using
        congrArg (fun result : List PrintPart × LS => (.text text :: result.1, result.2)) (ih before)
    | expr expression =>
      simpa only [List.cons_append, lowerPrintArgs, bind_run, pure_run] using
        congrArg (fun result : List PrintPart × LS =>
          (.val (lowerExpr expression env before).1 :: result.1, result.2))
          (ih (lowerExpr expression env before).2)

private theorem print_arguments_ready {module : GIR.Module} {func : Func} (state : State)
    (arguments : List PrintArg) (env : LEnv) (initial : LS)
    (step : ∀ earlier expression suffix, arguments = earlier ++ .expr expression :: suffix →
      ValueReadyAt state (lowerExpr expression) env (lowerPrintArgs earlier env initial).2 ∧
      EmitsOnly (ReadyCallObservations module func state) (lowerPrintArgs earlier env initial).2
        (lowerExpr expression env (lowerPrintArgs earlier env initial).2).2) :
    PrintArgumentsReadyAt state arguments env initial ∧
      EmitsOnly (ReadyCallObservations module func state) initial (lowerPrintArgs arguments env initial).2 := by
  induction arguments generalizing initial with
  | nil => exact ⟨⟨.refl _ _, by simp [lowerPrintArgs, pure_run]⟩, .refl _ _⟩
  | cons argument rest ih =>
    cases argument with
    | text text =>
      have tail := ih initial (by
        intro earlier expression suffix split
        have selected := step (.text text :: earlier) expression suffix (by simp [split])
        simpa only [lowerPrintArgs, bind_run, pure_run] using selected)
      refine ⟨⟨?_, ?_⟩, ReadyCallObservations.print_arguments_text text rest tail.2⟩
      · exact tail.1.1
      · intro live value member
        simp only [lowerPrintArgs, bind_run, pure_run] at member
        rcases List.mem_cons.mp member with impossible | later
        · cases impossible
        · exact tail.1.2 live value later
    | expr expression =>
      have first := step [] expression rest rfl
      simp only [lowerPrintArgs, pure_run] at first
      have tail := ih (lowerExpr expression env initial).2 (by
        intro earlier child suffix split
        have selected := step (.expr expression :: earlier) child suffix (by simp [split])
        simpa only [lowerPrintArgs, bind_run, pure_run] using selected)
      refine ⟨⟨?_, ?_⟩, ReadyCallObservations.print_arguments_expr expression rest first.2 tail.2⟩
      · exact first.1.1.trans tail.1.1
      · intro live value member
        simp only [lowerPrintArgs, bind_run, pure_run] at member
        rcases List.mem_cons.mp member with same | later
        · cases same
          exact first.1.2 ((dead_lowerPrintArgs rest).live_before rfl live)
        · exact tail.1.2 live value later

theorem print {arguments : List PrintArg}
    (source : Core.tyStmt typingEnv scope (.print arguments origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (native : NativeRows types (lowerStmt loop (.print arguments origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.print arguments origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.print arguments origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ earlier expression later type next last,
      arguments = earlier ++ .expr expression :: later →
      Core.tyPrintArgs typingEnv earlier start = .ok ((), next) →
      Core.tyExpr typingEnv expression next = .ok (type, last) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let prior := (lowerPrintArgs earlier env before).2
      GeneratedBuilderState prior → NativeRows types (lowerExpr expression env prior).2 →
      (lowerExpr expression env prior).2.Ext completed →
      (lowerExpr expression env prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) env prior ∧
      EmitsOnly (ReadyCallObservations module func state) prior
        ((lowerExpr expression) env prior).2) :
    (EmitsOnly (ReadyOperands state) before (lowerStmt loop (.print arguments origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.print arguments origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerStmt loop (.print arguments origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  obtain ⟨checked, outputEq⟩ := tyStmt_print_children source
  subst output
  have values := print_arguments_ready (module := module) (func := func) state arguments env before (by
    intro earlier expression later split
    have selected := checked
    rw [split] at selected
    obtain ⟨next, last, type, prefixChecked, expressionChecked⟩ := printArgs_split_source selected
    let printed := lowerPrintArgs earlier env before
    let value := lowerExpr expression env printed.2
    have tailTypes := TypeRun.bind (types_lowerPrintArgs later) fun parts =>
      types_emitEffect (.print (printed.1 ++ .val value.1 :: parts) (some origin))
    have tailAdvance := AdvB.bind (advB_lowerPrintArgs later) fun parts =>
      advB_emitEffect (.print (printed.1 ++ .val value.1 :: parts) (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames (child := value.2) native extension allocated
      (by rw [split]; simp only [lowerStmt, lower_print_args_append_run, lowerPrintArgs, bind_run, pure_run]; exact
        tailTypes env value.2 _ _ rfl)
      (by rw [split]; simp only [lowerStmt, lower_print_args_append_run, lowerPrintArgs, bind_run, pure_run]; exact
        tailAdvance env value.2 _ _ rfl)
    exact child earlier expression later type next last split prefixChecked expressionChecked
      (generated.lowerPrintArgs earlier rfl) childNative childExtension childAllocated visible)
  exact ⟨⟨ready_print (loop := loop) values.1, fun _ => visible⟩,
    ReadyCallObservations.statement_print arguments origin values.2⟩

end Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyStatementObservations

import Goose.Lower.Validation.SourceReadyTypedStatementsPrint

namespace Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyStatementFrames

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
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.letS slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.letS slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let value := lowerExpr expression env before
  apply frame.typedLet (loop := loop) source generated slotCount extension allocated visible
  · intro type next checked
    have tailTypes := TypeRun.bind (types_coerceSlot slot value.1 origin) fun converted => types_emitEffect (.slotInit slot converted (some origin))
    have tailAdvance := AdvB.bind (advB_coerceSlot slot value.1 origin) fun converted => advB_emitEffect (.slotInit slot converted (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact child type next checked (generated) childNative childExtension childAllocated visible

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
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.rebind slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.rebind slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let value := lowerExpr expression env before
  apply frame.typedRebind (loop := loop) source generated extension allocated visible
  · intro type checked
    have tailTypes := TypeRun.bind (types_coerceSlot slot value.1 origin) fun converted => TypeRun.bind (types_emitDef (.slotAddr slot)) fun address => types_emitEffect (.store address converted (some origin))
    have tailAdvance := AdvB.bind (advB_coerceSlot slot value.1 origin) fun converted => AdvB.bind (advB_emitDef (.slotAddr slot)) fun address => advB_emitEffect (.store address converted (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact child type checked (generated) childNative childExtension childAllocated visible

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
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.expr expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.expr expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let value := lowerExpr expression env before
  apply typed_ready_expression (loop := loop) source visible
  · intro type checked
    have tailTypes := TypeRun.pure ()
    have tailAdvance := AdvB.pure ()
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact child type checked (generated) childNative childExtension childAllocated visible

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
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.assertS expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.assertS expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let value := lowerExpr expression env before
  apply typed_ready_assert (loop := loop) source visible
  · intro checked
    have tailTypes := types_assert_core value.1 origin
    have tailAdvance := advB_assert_core value.1 origin
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact child checked (generated) childNative childExtension childAllocated visible

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
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.exit expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.exit expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let value := lowerExpr expression env before
  apply typed_ready_exit (loop := loop) source visible
  · intro integer checked
    have tailTypes := types_emitTerm (.exit value.1 (some origin))
    have tailAdvance := advB_emitTerm (.exit value.1 (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact child integer checked (generated) childNative childExtension childAllocated visible

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
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.ret (some expression) origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.ret (some expression) origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let value := lowerExpr expression env before
  apply frame.typedReturnSome (loop := loop) source generated extension allocated visible
  · intro type checked
    have tailTypes := TypeRun.bind (types_coerceResult value.1 origin) fun converted => TypeRun.bind (types_leaveTo 0) fun _ => types_emitTerm (.ret [converted] (some origin))
    have tailAdvance := AdvB.bind (advB_coerceResult value.1 origin) fun converted => AdvB.bind (advB_leaveTo 0) fun _ => advB_emitTerm (.ret [converted] (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact child type checked (generated) childNative childExtension childAllocated visible

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
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior)
    (valueChild : ∀ type next, Core.tyExpr typingEnv expression next = .ok (type, finish) →
      let prior := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2
      GeneratedBuilderState prior → NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.assign place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.assign place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  let value := lowerExpr expression env address.2
  apply typed_ready_assign (loop := loop) source visible
  · intro info next checked
    have tailTypes := TypeRun.bind (types_lowerExpr expression) fun v => types_emitEffect (.store address.1 v (some origin))
    have tailAdvance := AdvB.bind (advB_lowerExpr expression) fun v => advB_emitEffect (.store address.1 v (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact placeChild info next checked (generated) childNative childExtension childAllocated visible
  · intro type next checked
    have tailTypes := types_emitEffect (.store address.1 value.1 (some origin))
    have tailAdvance := advB_emitEffect (.store address.1 value.1 (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2 _ _ rfl)
    exact valueChild type next checked (generated.lowerPlace place rfl) childNative childExtension childAllocated visible

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
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior)
    (valueChild : ∀ integer next, Core.tyExpr typingEnv expression next = .ok (.int integer, finish) →
      let prior := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2
      GeneratedBuilderState prior → NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.popN place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.popN place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  let value := lowerExpr expression env address.2
  apply typed_ready_popN (loop := loop) source visible
  · intro info next checked
    have tailTypes := TypeRun.bind (types_lowerExpr expression) fun v => types_emitEffect (.popN address.1 v (some origin))
    have tailAdvance := AdvB.bind (advB_lowerExpr expression) fun v => advB_emitEffect (.popN address.1 v (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact placeChild info next checked (generated) childNative childExtension childAllocated visible
  · intro integer next checked
    have tailTypes := types_emitEffect (.popN address.1 value.1 (some origin))
    have tailAdvance := advB_emitEffect (.popN address.1 value.1 (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2 _ _ rfl)
    exact valueChild integer next checked (generated.lowerPlace place rfl) childNative childExtension childAllocated visible

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
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior)
    (viewChild : ∀ element writable next, Core.tyView typingEnv view next = .ok ((element, writable), finish) →
      let prior := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2
      GeneratedBuilderState prior → NativeRows types (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerView view) (lowerEnv typingEnv.mod typingEnv.vars results) prior) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.append place view origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.append place view origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  let value := lowerView view env address.2
  apply typed_ready_append (loop := loop) source visible
  · intro info next checked
    have tailTypes := TypeRun.bind (types_lowerView view) fun v => types_emitEffect (.append address.1 v (some origin))
    have tailAdvance := AdvB.bind (advB_lowerView view) fun v => advB_emitEffect (.append address.1 v (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact placeChild info next checked (generated) childNative childExtension childAllocated visible
  · intro element writable next checked
    have tailTypes := types_emitEffect (.append address.1 value.1 (some origin))
    have tailAdvance := advB_emitEffect (.append address.1 value.1 (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2) native extension allocated
      (by exact tailTypes env (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2 _ _ rfl)
      (by exact tailAdvance env (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2 _ _ rfl)
    exact viewChild element writable next checked (generated.lowerPlace place rfl) childNative childExtension childAllocated visible

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
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.clear place origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.clear place origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  apply typed_ready_clear (loop := loop) source visible
  · intro info checked
    have tailTypes := types_emitEffect (.clear address.1 (some origin))
    have tailAdvance := advB_emitEffect (.clear address.1 (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact child info checked (generated) childNative childExtension childAllocated visible

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
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior)
    (valueChild : ∀ type next, Core.tyExpr typingEnv expression next = .ok (type, finish) →
      let prior := (emitEffect (.clear (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).1 (some origin)) (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2
      GeneratedBuilderState prior → NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.assignWhole place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.assignWhole place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  let cleared := (emitEffect (.clear address.1 (some origin)) env address.2).2
  let value := lowerExpr expression env cleared
  apply typed_ready_assignWhole (loop := loop) source visible
  · intro info next checked
    have tailTypes := TypeRun.bind (types_emitEffect (.clear address.1 (some origin))) fun _ => TypeRun.bind (types_lowerExpr expression) fun v => types_emitEffect (.replace address.1 v (some origin))
    have tailAdvance := AdvB.bind (advB_emitEffect (.clear address.1 (some origin))) fun _ => AdvB.bind (advB_lowerExpr expression) fun v => advB_emitEffect (.replace address.1 v (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact placeChild info next checked (generated) childNative childExtension childAllocated visible
  · intro type next checked
    have tailTypes := types_emitEffect (.replace address.1 value.1 (some origin))
    have tailAdvance := advB_emitEffect (.replace address.1 value.1 (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (emitEffect (.clear (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).1 (some origin)) (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (emitEffect (.clear (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).1 (some origin)) (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (emitEffect (.clear (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).1 (some origin)) (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2).2 _ _ rfl)
    exact valueChild type next checked ((generated.lowerPlace place rfl).emitEffect _ rfl) childNative childExtension childAllocated visible

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
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) prior)
    (valueChild : ∀ integer next, Core.tyExpr typingEnv expression next = .ok (.int integer, finish) →
      let prior := (Lower.emitDef (.load (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).1) (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2
      GeneratedBuilderState prior → NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) prior) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.assignOp operation place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.assignOp operation place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true → VisibleSlotsReady output state) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  let loaded := Lower.emitDef (.load address.1) env address.2
  let value := lowerExpr expression env loaded.2
  apply frame.typedAssignOp (loop := loop) source generated native extension allocated visible
  · intro info next checked
    have tailTypes := TypeRun.bind (types_emitDef (.load address.1)) fun old => TypeRun.bind (types_lowerExpr expression) fun rhs => TypeRun.bind (types_intTyOf old) fun t => TypeRun.bind (types_emitDef (.bin operation t old rhs (some origin))) fun v => types_emitEffect (.store address.1 v (some origin))
    have tailAdvance := AdvB.bind (advB_emitDef (.load address.1)) fun old => AdvB.bind (advB_lowerExpr expression) fun rhs => AdvB.bind (advB_intTyOf old) fun t => AdvB.bind (advB_emitDef (.bin operation t old rhs (some origin))) fun v => advB_emitEffect (.store address.1 v (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2) native extension allocated
      (by exact tailTypes env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
      (by exact tailAdvance env (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 _ _ rfl)
    exact placeChild info next checked (generated) childNative childExtension childAllocated visible
  · intro integer next checked
    have tailTypes := TypeRun.bind (types_intTyOf loaded.1) fun t => TypeRun.bind (types_emitDef (.bin operation t loaded.1 value.1 (some origin))) fun v => types_emitEffect (.store address.1 v (some origin))
    have tailAdvance := AdvB.bind (advB_intTyOf loaded.1) fun t => AdvB.bind (advB_emitDef (.bin operation t loaded.1 value.1 (some origin))) fun v => advB_emitEffect (.store address.1 v (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames
      (child := (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (Lower.emitDef (.load (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).1) (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2).2) native extension allocated
      (by exact tailTypes env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (Lower.emitDef (.load (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).1) (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2).2 _ _ rfl)
      (by exact tailAdvance env (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) (Lower.emitDef (.load (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).1) (lowerEnv typingEnv.mod typingEnv.vars results) (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2).2 _ _ rfl)
    exact valueChild integer next checked ((generated.lowerPlace place rfl).emitDef _ rfl) childNative childExtension childAllocated visible

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
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before)
    (sizeChild : ∀ integer next last, Core.tyExpr typingEnv size next = .ok (.int integer, last) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let prior := (lowerPlace place env before).2
      GeneratedBuilderState prior → NativeRows types (lowerExpr size env prior).2 →
      (lowerExpr size env prior).2.Ext completed →
      (lowerExpr size env prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr size) env prior)
    (fillChild : ∀ expression type next, fill = some expression →
      Core.tyExpr typingEnv expression next = .ok (type, finish) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let prior := (lowerExpr size env (lowerPlace place env before).2).2
      GeneratedBuilderState prior → NativeRows types (lowerExpr expression env prior).2 →
      (lowerExpr expression env prior).2.Ext completed →
      (lowerExpr expression env prior).2.vals.size ≤ completed.vals.size → VisibleSlotsReady typingEnv state →
      ValueReadyAt state (lowerExpr expression) env prior) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.resize place size fill origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.resize place size fill origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
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
  apply typed_ready_resize (loop := loop) source visible
  · intro info next checked
    have tailTypes := TypeRun.bind (types_lowerExpr size) fun n => TypeRun.bind fillingTypes fun f =>
      types_emitEffect (.resize address.1 n f (some origin))
    have tailAdvance := AdvB.bind (advB_lowerExpr size) fun n => AdvB.bind fillingAdvance fun f =>
      advB_emitEffect (.resize address.1 n f (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames (child := address.2) native extension allocated
      (by cases fill <;> exact tailTypes env address.2 _ _ rfl)
      (by cases fill <;> exact tailAdvance env address.2 _ _ rfl)
    exact placeChild info next checked generated childNative childExtension childAllocated visible
  · intro integer next last checked
    have tailTypes := TypeRun.bind fillingTypes fun f => types_emitEffect (.resize address.1 sized.1 f (some origin))
    have tailAdvance := AdvB.bind fillingAdvance fun f => advB_emitEffect (.resize address.1 sized.1 f (some origin))
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames (child := sized.2) native extension allocated
      (by cases fill <;> exact tailTypes env sized.2 _ _ rfl)
      (by cases fill <;> exact tailAdvance env sized.2 _ _ rfl)
    exact sizeChild integer next last checked (generated.lowerPlace place rfl) childNative childExtension childAllocated visible
  · intro expression type next same checked
    subst fill
    let value := lowerExpr expression env sized.2
    obtain ⟨childNative, childExtension, childAllocated⟩ := child_frames (child := value.2) native extension allocated
      (by exact
        types_emitEffect (.resize address.1 sized.1 (some value.1) (some origin)) env value.2 _ _ rfl)
      (by exact
        advB_emitEffect (.resize address.1 sized.1 (some value.1) (some origin)) env value.2 _ _ rfl)
    exact fillChild expression type next rfl checked ((generated.lowerPlace place rfl).lowerExpr size rfl)
      childNative childExtension childAllocated visible

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
      ValueReadyAt state (lowerExpr expression) env prior) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.print arguments origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.print arguments origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  apply typed_ready_print (loop := loop) source visible
  intro earlier expression later type next last split prefixChecked checked
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
  exact child earlier expression later type next last split prefixChecked checked (generated.lowerPrintArgs earlier rfl)
    childNative childExtension childAllocated visible

end Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyStatementFrames

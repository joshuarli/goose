import Goose.Lower.Validation.SourceReadyTypedStatementsMutations

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before : LS}
  {typingEnv output : TEnv} {results : List Ty} {loop : Option LoopCtx}
  {scope start finish : Nat} {origin : OriginId}

theorem SourceReadyFrame.typedLet {slot : SlotId} {expression : Expr}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyStmt typingEnv scope (.letS slot expression origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (slotCount : func.slots.size = typingEnv.vars.size)
    (extension : (lowerStmt loop (.letS slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.letS slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ type next, Core.tyExpr typingEnv expression next = .ok (type, finish) →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.letS slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.letS slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  obtain ⟨localVar, type, next, declared, expressionSource, _, outputEq⟩ := tyStmt_let_children source
  subst output
  have variableRow := (declare_ok _ _ _ _ _ declared).2.1
  have slotBound : slot < func.slots.size := by
    rw [slotCount]
    exact (Array.getElem?_eq_some_iff.mp variableRow).1
  exact frame.letS (loop := loop) rfl rfl extension allocated
    (generated.lowerExpr expression rfl).live slotBound visible (child type next expressionSource)

theorem SourceReadyFrame.typedRebind {slot : SlotId} {expression : Expr}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyStmt typingEnv scope (.rebind slot expression origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (extension : (lowerStmt loop (.rebind slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.rebind slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ type, Core.tyExpr typingEnv expression start = .ok (type, finish) →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.rebind slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.rebind slot expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  obtain ⟨localVar, type, _, _, _, _, checked, _, outputEq⟩ := tyStmt_rebind_children source
  subst output
  exact ⟨frame.rebind (loop := loop) extension allocated (generated.lowerExpr expression rfl).live (child type checked), fun _ => visible⟩

theorem SourceReadyFrame.typedAssignOp {place : Place} {expression : Expr} {operation : BinOp}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyStmt typingEnv scope (.assignOp operation place expression origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerStmt loop (.assignOp operation place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.assignOp operation place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.assignOp operation place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (placeChild : ∀ info next, Core.tyPlace typingEnv place start = .ok (info, next) →
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before)
    (valueChild : ∀ integer next, Core.tyExpr typingEnv expression next = .ok (.int integer, finish) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let address := lowerPlace place env before
      let loaded := Lower.emitDef (.load address.1) env address.2
      ValueReadyAt state (lowerExpr expression) env loaded.2) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.assignOp operation place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.assignOp operation place expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  obtain ⟨info, integer, next, placeSource, integerType, valueSource, _, outputEq⟩ := tyStmt_assignOp_children source
  subst output
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  let loaded := Lower.emitDef (.load address.1) env address.2
  let tail : B Unit := do
    let rhs ← lowerExpr expression
    let type ← intTyOf loaded.1
    let result ← Lower.emitDef (.bin operation type loaded.1 rhs (some origin))
    emitEffect (.store address.1 result (some origin))
  have tailTypes : TypeRun tail := by
    apply TypeRun.bind (types_lowerExpr expression)
    intro rhs
    apply TypeRun.bind (types_intTyOf loaded.1)
    intro type
    apply TypeRun.bind (types_emitDef (.bin operation type loaded.1 rhs (some origin)))
    intro value
    exact types_emitEffect (.store address.1 value (some origin))
  have actualNative : SummaryPreservation.NativeRows types (tail env loaded.2).2 := by
    simpa only [tail, lowerStmt, bind_run, env, address, loaded] using native
  have loadedNative : SummaryPreservation.NativeRows types loaded.2 :=
    actualNative.of_prefix (tailTypes env loaded.2 _ _ rfl)
  have scalar := scalarLoadedPlace (results := results) placeSource integerType generated loadedNative
  exact ⟨frame.assignOp (loop := loop) extension allocated (generated.lowerPlace place rfl).live scalar
    (placeChild info next placeSource) (valueChild integer next valueSource), fun _ => visible⟩

end Goose.Lower.Validation.ReplacementContentFlowSource

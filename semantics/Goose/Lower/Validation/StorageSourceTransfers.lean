import Goose.Lower.Validation.StorageSourceOutputs
import Goose.Lower.Validation.StorageSourceControl
import Goose.Lower.Validation.SourceStatementTypingTransfers

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem storage_let_source {env output : Core.TEnv} {results : List Ty} {slot : VarId}
    {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.letS slot expr origin) start = .ok (output, finish))
    (child : StorageExprChild env results expr) (loop : Option LoopCtx)
    {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.letS slot expr origin)) := by
  obtain ⟨localVar, childType, childStart, _, childSource, _, _⟩ := tyStmt_let_children source
  exact (child childSource generated).bind ((StorageAt.coerceSlot _ _ _ _ _).bind
    (StorageAt.emitEffect _ (by intros; trivial)))

theorem storage_expr_source {env output : Core.TEnv} {results : List Ty}
    {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.expr expr origin) start = .ok (output, finish))
    (child : StorageExprChild env results expr) (loop : Option LoopCtx)
    {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.expr expr origin)) := by
  obtain ⟨type, childSource, _⟩ := tyStmt_expr_children source
  exact (child childSource generated).bind (StorageAt.pure _ _ _)

theorem storage_return_source {env output : Core.TEnv} {results : List Ty}
    {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.ret (some expr) origin) start = .ok (output, finish))
    (child : StorageExprChild env results expr) (loop : Option LoopCtx)
    {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.ret (some expr) origin)) := by
  obtain ⟨expected, actual, impl, _, _, _, childSource, _, _⟩ := tyStmt_return_children source
  unfold lowerStmt
  apply (child childSource generated).bind
  apply (StorageAt.coerceResult _ _ _ _).bind
  apply (StorageAt.pure _ _ _).bind
  exact (StorageAt.leaveTo _ _ _).bind (StorageAt.emitTerm _ _ _)

theorem StorageAt.return_none (le : LEnv) (before : LS) (loop : Option LoopCtx) (origin : OriginId) :
    StorageAt le before (lowerStmt loop (.ret none origin)) :=
  (StorageAt.pure _ _ _).bind ((StorageAt.leaveTo _ _ _).bind (StorageAt.emitTerm _ _ _))

theorem StorageAt.breakStmt (le : LEnv) (before : LS) (loop : Option LoopCtx) (origin : OriginId) :
    StorageAt le before (lowerStmt loop (.brk origin)) := by
  cases loop with
  | none => exact StorageAt.pure _ _ _
  | some loop => exact (StorageAt.leaveTo _ _ _).bind (StorageAt.emitTerm _ _ _)

theorem StorageAt.continueStmt (le : LEnv) (before : LS) (loop : Option LoopCtx) (origin : OriginId) :
    StorageAt le before (lowerStmt loop (.cont origin)) := by
  cases loop with
  | none => exact StorageAt.pure _ _ _
  | some loop =>
    apply (StorageAt.leaveTo _ _ _).bind
    cases loop.cont with
    | jump header => exact StorageAt.emitTerm _ _ _
    | next header type value => exact (StorageAt.emitDef _ (by intros; trivial)).bind (StorageAt.emitTerm _ _ _)

theorem storage_assert_source {env output : Core.TEnv} {results : List Ty}
    {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assertS expr origin) start = .ok (output, finish))
    (child : StorageExprChild env results expr) (loop : Option LoopCtx)
    {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.assertS expr origin)) := by
  have childSource := (tyStmt_assert_children source).1
  apply (child childSource generated).bind
  apply StorageAt.whenLive
  intro block live
  exact (StorageAt.fork _ _ _).bind ((StorageAt.setCur _ _ _).bind
    ((StorageAt.emitTerm _ _ _).bind (StorageAt.setCur _ _ _)))

theorem storage_exit_source {env output : Core.TEnv} {results : List Ty}
    {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.exit expr origin) start = .ok (output, finish))
    (child : StorageExprChild env results expr) (loop : Option LoopCtx)
    {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.exit expr origin)) := by
  obtain ⟨integer, childSource, _⟩ := tyStmt_exit_children source
  exact (child childSource generated).bind (StorageAt.emitTerm _ _ _)

end Goose.Lower.Validation

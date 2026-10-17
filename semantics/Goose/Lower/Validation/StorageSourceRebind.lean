import Goose.Lower.Validation.StorageSourceStatements
import Goose.Lower.Validation.SourceReadable

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem storage_rebind_source {env output : Core.TEnv} {results : List Ty}
    {slot : VarId} {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.rebind slot expr origin) start = .ok (output, finish))
    (sourceTypes : SourceReadableEnvironment env)
    (exprChild : StorageExprChild env results expr)
    (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.rebind slot expr origin)) := by
  obtain ⟨localVar, childType, row, _, reference, mutable, childSource, passable, _⟩ := tyStmt_rebind_children source
  have readable := source_passable_expression_readable expr sourceTypes childSource passable reference
  let le := lowerEnv env.mod env.vars results
  let value := lowerExpr expr le before
  let coerced := Goose.Lower.coerceSlot slot value.1 origin le value.2
  have slotRow : le.slots[slot]? = some ⟨localVar.ty, localVar.kind, localVar.scope, slot⟩ := by
    simp [le, lowerEnv, Array.getElem?_mapIdx, row]
  have operation : (Op.slotAddr slot).resultTy (tyEnv le coerced.2) = .ok (.data (.ref .mutable localVar.ty)) := by
    simp only [Op.resultTy, tyEnv, slotRow, mutable]
    cases shape : localVar.ty <;> simp only [shape, Ty.isRefLike, Bool.false_eq_true] at reference
    all_goals rfl
  change StorageAt _ _ (lowerExpr expr >>= fun value => do
    let value ← coerceSlot slot value origin
    let address ← emitDef (.slotAddr slot)
    emitEffect (.store address value (some origin)))
  apply (exprChild childSource generated).bind
  apply (StorageAt.coerceSlot _ _ _ _ _).bind
  apply (StorageAt.emitDef _ (by intros; trivial)).bind
  apply StorageAt.emitEffect
  intro active
  have coercedLive : coerced.2.cur.isSome = true :=
    (dead_emitDef (.slotAddr slot)).live_before (le := le) (before := coerced.2) rfl active
  cases current : coerced.2.cur with
  | none => simp [current] at coercedLive
  | some block =>
    have recorded := emitDef_recorded current operation
    exact ⟨localVar.ty, recorded.2.2.1, readable⟩

end Goose.Lower.Validation

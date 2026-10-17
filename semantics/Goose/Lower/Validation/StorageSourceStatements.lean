import Goose.Lower.Validation.StorageSourceOutputs
import Goose.Lower.Validation.StorageSourceCoercions
import Goose.Lower.Validation.SourceStatementTypingStorage

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem storage_assign_source {env output : Core.TEnv} {results : List Ty}
    (outputs : StorageSourceOutputs env results) {place : Place} {expr : Expr} {origin : OriginId}
    {scope start finish : Nat} (source : Core.tyStmt env scope (.assign place expr origin) start = .ok (output, finish))
    (placeChild : StoragePlaceChild env results place) (exprChild : StorageExprChild env results expr)
    (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.assign place expr origin)) := by
  obtain ⟨info, childStart, placeSource, childSource, copyable, writable, _⟩ := tyStmt_assign_children source
  have readable : info.ty.readable = true := by
    apply flat_or_slice_readable
    rcases (show info.ty.flat = true ∨ info.ty.isSlice = true ∧ place.derefVar?.isSome = true from by
      simpa only [Bool.or_eq_true, Bool.and_eq_true] using copyable) with flat | ⟨slice, _⟩
    · exact Or.inl flat
    · exact Or.inr slice
  let address := lowerPlace place (lowerEnv env.mod env.vars results) before
  have addressGenerated := generated.lowerPlace place (show lowerPlace place _ before = address from rfl)
  change StorageAt _ _ (lowerPlace place >>= fun address => do
    let value ← lowerExpr expr
    emitEffect (.store address value (some origin)))
  apply (placeChild placeSource generated).bind
  apply (exprChild childSource addressGenerated).bind
  apply StorageAt.emitEffect
  intro active
  have addressLive := (dead_lowerExpr expr).live_before rfl active
  have permission : info.referenceWritable env.mod.profile = true := by
    rw [readable_referenceWritable readable]; exact writable
  have row := outputs.writablePlace place placeSource permission generated rfl addressLive
  exact ⟨info.ty, types_lowerExpr expr _ address.2 _ _ rfl _ _ row, readable⟩

theorem storage_append_source {env output : Core.TEnv} {results : List Ty}
    (outputs : StorageSourceOutputs env results) {owner : Place} {view : View} {origin : OriginId}
    {scope start finish : Nat} (source : Core.tyStmt env scope (.append owner view origin) start = .ok (output, finish))
    (placeChild : StoragePlaceChild env results owner) (viewChild : StorageViewChild env results view)
    (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.append owner view origin)) := by
  obtain ⟨info, element, writable, childStart, placeSource, elementShape, viewSource, _, _⟩ := tyStmt_append_children source
  let address := lowerPlace owner (lowerEnv env.mod env.vars results) before
  have addressGenerated := generated.lowerPlace owner (show lowerPlace owner _ before = address from rfl)
  change StorageAt _ _ (lowerPlace owner >>= fun address => do
    let value ← lowerView view
    emitEffect (.append address value (some origin)))
  apply (placeChild placeSource generated).bind
  apply (viewChild viewSource addressGenerated).bind
  apply StorageAt.emitEffect
  intro active
  have addressLive := (dead_lowerView view).live_before rfl active
  obtain ⟨mu, row⟩ := outputs.place owner placeSource generated rfl addressLive
  exact ⟨mu, info.ty, types_lowerView view _ address.2 _ _ rfl _ _ row, Or.inr (by simp [elementShape])⟩

theorem storage_clear_source {env output : Core.TEnv} {results : List Ty}
    (outputs : StorageSourceOutputs env results) {owner : Place} {origin : OriginId}
    {scope start finish : Nat} (source : Core.tyStmt env scope (.clear owner origin) start = .ok (output, finish))
    (placeChild : StoragePlaceChild env results owner)
    (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.clear owner origin)) := by
  obtain ⟨info, element, placeSource, elementShape, _, _⟩ := tyStmt_clear_children source
  change StorageAt _ _ (lowerPlace owner >>= fun address => emitEffect (.clear address (some origin)))
  apply (placeChild placeSource generated).bind
  apply StorageAt.emitEffect
  intro active
  obtain ⟨mu, row⟩ := outputs.place owner placeSource generated rfl active
  exact ⟨mu, info.ty, row, Or.inr ⟨tyStmt_clear_profile source, by simp [elementShape]⟩⟩

theorem storage_popN_source {env output : Core.TEnv} {results : List Ty}
    (outputs : StorageSourceOutputs env results) {owner : Place} {count : Expr} {origin : OriginId}
    {scope start finish : Nat} (source : Core.tyStmt env scope (.popN owner count origin) start = .ok (output, finish))
    (placeChild : StoragePlaceChild env results owner) (exprChild : StorageExprChild env results count)
    (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.popN owner count origin)) := by
  obtain ⟨info, element, integer, childStart, placeSource, elementShape, countSource, _, _⟩ := tyStmt_popN_children source
  let address := lowerPlace owner (lowerEnv env.mod env.vars results) before
  have addressGenerated := generated.lowerPlace owner (show lowerPlace owner _ before = address from rfl)
  change StorageAt _ _ (lowerPlace owner >>= fun address => do
    let value ← lowerExpr count
    emitEffect (.popN address value (some origin)))
  apply (placeChild placeSource generated).bind
  apply (exprChild countSource addressGenerated).bind
  apply StorageAt.emitEffect
  intro active
  have addressLive := (dead_lowerExpr count).live_before rfl active
  obtain ⟨mu, row⟩ := outputs.place owner placeSource generated rfl addressLive
  exact ⟨mu, info.ty, types_lowerExpr count _ address.2 _ _ rfl _ _ row,
    Or.inr ⟨tyStmt_popN_profile source, by simp [elementShape]⟩⟩

theorem storage_assignWhole_source {env output : Core.TEnv} {results : List Ty}
    (outputs : StorageSourceOutputs env results) {owner : Place} {expr : Expr} {origin : OriginId}
    {scope start finish : Nat} (source : Core.tyStmt env scope (.assignWhole owner expr origin) start = .ok (output, finish))
    (placeChild : StoragePlaceChild env results owner) (exprChild : StorageExprChild env results expr)
    (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.assignWhole owner expr origin)) := by
  obtain ⟨info, element, childStart, placeSource, shape, childSource, _, _, _⟩ := tyStmt_assignWhole_children source
  let address := lowerPlace owner (lowerEnv env.mod env.vars results) before
  let cleared := emitEffect (.clear address.1 (some origin)) (lowerEnv env.mod env.vars results) address.2
  have addressGenerated := generated.lowerPlace owner (show lowerPlace owner _ before = address from rfl)
  have clearedGenerated := addressGenerated.emitEffect (.clear address.1 (some origin))
    (show emitEffect _ _ address.2 = cleared from rfl)
  change StorageAt _ _ (lowerPlace owner >>= fun address => do
    emitEffect (.clear address (some origin))
    let value ← lowerExpr expr
    emitEffect (.replace address value (some origin)))
  apply (placeChild placeSource generated).bind
  apply StorageAt.bind
  · apply StorageAt.emitEffect
    intro active
    obtain ⟨mu, row⟩ := outputs.place owner placeSource generated rfl active
    refine ⟨mu, info.ty, row, Or.inr ⟨tyStmt_assignWhole_profile source, ?_⟩⟩
    rcases shape with same | same <;> simp [same, Ty.ownerElem?]
  · apply (exprChild childSource clearedGenerated).bind
    apply StorageAt.emitEffect
    intro active
    have clearedLive := (dead_lowerExpr expr).live_before rfl active
    have addressLive := (dead_emitEffect (.clear address.1 (some origin))).live_before rfl clearedLive
    obtain ⟨mu, row⟩ := outputs.place owner placeSource generated rfl addressLive
    have clearedRow : cleared.2.vals[address.1]? = some (some (.data (.ref mu info.ty))) :=
      types_emitEffect (.clear address.1 (some origin)) _ address.2 _ _ rfl _ _ row
    exact ⟨mu, info.ty, types_lowerExpr expr _ cleared.2 _ _ rfl _ _ clearedRow,
      Or.inr ⟨tyStmt_assignWhole_profile source, element, shape⟩⟩

theorem storage_assignOp_source {env output : Core.TEnv} {results : List Ty}
    (outputs : StorageSourceOutputs env results) {place : Place} {expr : Expr} {operation : BinOp} {origin : OriginId}
    {scope start finish : Nat} (source : Core.tyStmt env scope (.assignOp operation place expr origin) start = .ok (output, finish))
    (placeChild : StoragePlaceChild env results place) (exprChild : StorageExprChild env results expr)
    (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.assignOp operation place expr origin)) := by
  obtain ⟨info, integer, childStart, placeSource, integerShape, childSource, writable, _⟩ := tyStmt_assignOp_children source
  have readable : info.ty.readable = true := by simp [integerShape, Ty.readable, Ty.flat]
  have permission : info.referenceWritable env.mod.profile = true := by
    rw [readable_referenceWritable readable]; exact writable
  let le := lowerEnv env.mod env.vars results
  let address := lowerPlace place le before
  let loaded := emitDef (.load address.1) le address.2
  let rhs := lowerExpr expr le loaded.2
  let kind := intTyOf loaded.1 le rhs.2
  let binary := emitDef (.bin operation kind.1 loaded.1 rhs.1 (some origin)) le kind.2
  have addressGenerated := generated.lowerPlace place (show lowerPlace place le before = address from rfl)
  have loadedGenerated := addressGenerated.emitDef (.load address.1) (show emitDef _ le address.2 = loaded from rfl)
  change StorageAt _ _ (lowerPlace place >>= fun address => do
    let old ← emitDef (.load address)
    let value ← lowerExpr expr
    let result ← emitDef (.bin operation (← intTyOf old) old value (some origin))
    emitEffect (.store address result (some origin)))
  apply (placeChild placeSource generated).bind
  apply StorageAt.bind
  · apply StorageAt.emitDef
    intro active value
    exact ⟨.mutable, info.ty, outputs.writablePlace place placeSource permission generated rfl active,
      Or.inl readable⟩
  · apply (exprChild childSource loadedGenerated).bind
    apply (StorageAt.intTyOf _ _ _).bind
    apply (StorageAt.emitDef _ (by intros; trivial)).bind
    apply StorageAt.emitEffect
    intro active
    have kindLive := (dead_emitDef (.bin operation kind.1 loaded.1 rhs.1 (some origin))).live_before rfl active
    have rhsLive := (dead_intTyOf loaded.1).live_before rfl kindLive
    have loadedLive := (dead_lowerExpr expr).live_before rfl rhsLive
    have addressLive := (dead_emitDef (.load address.1)).live_before rfl loadedLive
    have row := outputs.writablePlace place placeSource permission generated rfl addressLive
    have loadedRow : loaded.2.vals[address.1]? = some (some (.data (.ref .mutable info.ty))) :=
      types_emitDef (.load address.1) le address.2 loaded.1 loaded.2 rfl _ _ row
    have rhsRow : rhs.2.vals[address.1]? = some (some (.data (.ref .mutable info.ty))) :=
      types_lowerExpr expr le loaded.2 rhs.1 rhs.2 rfl _ _ loadedRow
    have kindRow : kind.2.vals[address.1]? = some (some (.data (.ref .mutable info.ty))) :=
      types_intTyOf loaded.1 le rhs.2 kind.1 kind.2 rfl _ _ rhsRow
    exact ⟨info.ty, types_emitDef (.bin operation kind.1 loaded.1 rhs.1 (some origin))
      le kind.2 binary.1 binary.2 rfl _ _ kindRow, readable⟩

#print axioms storage_assign_source
#print axioms storage_assignOp_source
#print axioms storage_append_source
#print axioms storage_popN_source
#print axioms storage_clear_source
#print axioms storage_assignWhole_source

end Goose.Lower.Validation

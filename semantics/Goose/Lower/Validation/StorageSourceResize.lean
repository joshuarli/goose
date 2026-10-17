import Goose.Lower.Validation.StorageSourceStatements

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem storage_resize_source {env output : Core.TEnv} {results : List Ty}
    (outputs : StorageSourceOutputs env results) {owner : Place} {size : Expr} {fill : Option Expr} {origin : OriginId}
    {scope start finish : Nat} (source : Core.tyStmt env scope (.resize owner size fill origin) start = .ok (output, finish))
    (placeChild : StoragePlaceChild env results owner) (sizeChild : StorageExprChild env results size)
    (fillChild : ∀ expr, fill = some expr → StorageExprChild env results expr)
    (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.resize owner size fill origin)) := by
  cases fill with
  | none =>
    obtain ⟨info, element, integer, childStart, sizeFinish, placeSource, elementShape, sizeSource, _, _, _⟩ :=
      tyStmt_resize_children source
    let address := lowerPlace owner (lowerEnv env.mod env.vars results) before
    have addressGenerated := generated.lowerPlace owner (show lowerPlace owner _ before = address from rfl)
    change StorageAt _ _ (lowerPlace owner >>= fun address => do
      let count ← lowerExpr size
      let filling : Option ValueId ← pure none
      emitEffect (.resize address count filling (some origin)))
    apply (placeChild placeSource generated).bind
    apply (sizeChild sizeSource addressGenerated).bind
    apply (StorageAt.pure _ _ _).bind
    apply StorageAt.emitEffect
    intro active
    have addressLive := (dead_lowerExpr size).live_before rfl active
    obtain ⟨mu, row⟩ := outputs.place owner placeSource generated rfl addressLive
    exact ⟨mu, info.ty, types_lowerExpr size _ address.2 _ _ rfl _ _ row,
      Or.inr ⟨tyStmt_resize_profile source, by simp [elementShape]⟩⟩
  | some expr =>
    obtain ⟨info, element, integer, childStart, sizeFinish, placeSource, elementShape, sizeSource, fillSource, _, _⟩ :=
      tyStmt_resize_children source
    let address := lowerPlace owner (lowerEnv env.mod env.vars results) before
    let count := lowerExpr size (lowerEnv env.mod env.vars results) address.2
    have addressGenerated := generated.lowerPlace owner (show lowerPlace owner _ before = address from rfl)
    have countGenerated := addressGenerated.lowerExpr size (show lowerExpr size _ address.2 = count from rfl)
    change StorageAt _ _ (lowerPlace owner >>= fun address => do
      let count ← lowerExpr size
      let filling ← (do pure (some (← lowerExpr expr)))
      emitEffect (.resize address count filling (some origin)))
    apply (placeChild placeSource generated).bind
    apply (sizeChild sizeSource addressGenerated).bind
    apply StorageAt.bind
    · exact (fillChild expr rfl fillSource countGenerated).bind (StorageAt.pure _ _ _)
    · apply StorageAt.emitEffect
      intro active
      have countLive := (dead_lowerExpr expr).live_before rfl active
      have addressLive := (dead_lowerExpr size).live_before rfl countLive
      obtain ⟨mu, row⟩ := outputs.place owner placeSource generated rfl addressLive
      have countRow : count.2.vals[address.1]? = some (some (.data (.ref mu info.ty))) :=
        types_lowerExpr size _ address.2 _ _ rfl _ _ row
      exact ⟨mu, info.ty, types_lowerExpr expr _ count.2 _ _ rfl _ _ countRow,
        Or.inr ⟨tyStmt_resize_profile source, by simp [elementShape]⟩⟩

end Goose.Lower.Validation

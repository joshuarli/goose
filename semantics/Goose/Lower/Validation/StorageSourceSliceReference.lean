import Goose.Lower.Validation.StorageSourceOutputs

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem storage_sliceRef_source {env : Core.TEnv} {results : List Ty}
    (outputs : StorageSourceOutputs env results) {expr : Expr} {type : Ty}
    (shortcut : Core.sliceRefTy env expr = some type) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerExpr expr) := by
  cases expr with
  | read place =>
    cases place with
    | var slot =>
      by_cases visible : slot ∈ env.visible
      · cases row : env.vars[slot]? with
        | none => simp [Core.sliceRefTy, visible, row] at shortcut
        | some localVar =>
          have reference : localVar.ty.isRefSlice = true := by
            by_cases reference : localVar.ty.isRefSlice = true
            · exact reference
            · simp [Core.sliceRefTy, visible, row, reference] at shortcut
          have placeSource : Core.tyPlace env (.var slot) 0 =
              .ok (⟨localVar.ty, localVar.kind == .mutable, true⟩, 0) := by
            simp [Core.tyPlace, Core.varOf, visible, row, pure, StateT.pure, Except.pure, bind, StateT.bind, Except.bind]
          change StorageAt _ _ (do
            let address ← emitDef (.slotAddr slot)
            let value ← emitDef (.load address)
            recordReadValueRootRecipe value (.var slot)
            pure value)
          apply (StorageAt.emitDef _ (by intros; trivial)).bind
          apply StorageAt.bind
          · apply StorageAt.emitDef
            intro active result
            obtain ⟨mu, typed⟩ := outputs.place (.var slot) placeSource generated rfl active
            exact ⟨mu, localVar.ty, typed, Or.inr reference⟩
          · exact (StorageAt.recordReadValueRootRecipe _ _ _ _).bind (StorageAt.pure _ _ _)
      · simp [Core.sliceRefTy, visible] at shortcut
    | _ => simp [Core.sliceRefTy] at shortcut
  | _ => simp [Core.sliceRefTy] at shortcut

#print axioms storage_sliceRef_source

end Goose.Lower.Validation

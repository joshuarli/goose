import Goose.Lower.Validation.ReplacementSourceSitesOutputs

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem replacementSites_sliceRef_source {env : Core.TEnv} {results : List Ty}
    {expr : Expr} {type : Ty}
    (shortcut : Core.sliceRefTy env expr = some type) {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (lowerEnv env.mod env.vars results) before (lowerExpr expr) := by
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
          change ReplacementSitesAt _ _ (emitDef (.slotAddr slot) >>= fun address => emitDef (.load address))
          apply (ReplacementSitesAt.emitDef _ (by intros; trivial)).bind
          exact ReplacementSitesAt.emitDef _ (by intros; trivial)
      · simp [Core.sliceRefTy, visible] at shortcut
    | _ => simp [Core.sliceRefTy] at shortcut
  | _ => simp [Core.sliceRefTy] at shortcut

end Goose.Lower.Validation

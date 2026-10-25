import Goose.Lower.Validation.ReplacementSourceSitesOutputs

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {root : DemandNode} {targets : List BlockId}

theorem replacementSites_sliceRef_source {env : Core.TEnv} {results : List Ty}
    {expr : Expr} {type : Ty}
    (shortcut : Core.sliceRefTy env expr = some type) {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerExpr expr) := by
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
          change ReplacementSitesAt (root := root) (targets := targets) _ _ (emitDef (.slotAddr slot) >>= fun address => do
            let value ← emitDef (.load address)
            recordReadValueRootRecipe value (.var slot)
            pure value)
          apply (ReplacementSitesAt.emitDef _ (by intros; trivial)).bind
          apply (ReplacementSitesAt.emitDef _ (by intros; trivial)).bind
          apply (ReplacementSitesAt.recordReadValueRootRecipe _ _ _ _).bind
          exact ReplacementSitesAt.pure _ _ _
      · simp [Core.sliceRefTy, visible] at shortcut
    | _ => simp [Core.sliceRefTy] at shortcut
  | _ => simp [Core.sliceRefTy] at shortcut

end Goose.Lower.Validation

import Goose.Lower.Validation.ReplacementSourceSitesStatements

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {targets : List BlockId}

theorem replacementSites_resize_source {env output : Core.TEnv} {results : List Ty}
    {owner : Place} {size : Expr} {fill : Option Expr} {origin : OriginId}
    {scope start finish : Nat} (source : Core.tyStmt env scope (.resize owner size fill origin) start = .ok (output, finish))
    (placeChild : ReplacementSitesPlaceChild (targets := targets) env results owner) (sizeChild : ReplacementSitesExprChild (targets := targets) env results size)
    (fillChild : ∀ expr, fill = some expr → ReplacementSitesExprChild (targets := targets) env results expr)
    (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (targets := targets) (lowerEnv env.mod env.vars results) before (lowerStmt loop (.resize owner size fill origin)) := by
  cases fill with
  | none =>
    obtain ⟨info, element, integer, childStart, sizeFinish, placeSource, elementShape, sizeSource, _, _, _⟩ :=
      tyStmt_resize_children source
    let address := lowerPlace owner (lowerEnv env.mod env.vars results) before
    have addressGenerated := generated.lowerPlace owner (show lowerPlace owner _ before = address from rfl)
    change ReplacementSitesAt (targets := targets) _ _ (lowerPlace owner >>= fun address => do
      let count ← lowerExpr size
      let filling : Option ValueId ← pure none
      emitEffect (.resize address count filling (some origin)))
    apply (placeChild placeSource generated).bind
    apply (sizeChild sizeSource addressGenerated).bind
    apply (ReplacementSitesAt.pure _ _ _).bind
    exact ReplacementSitesAt.emitEffect _ (by intros; trivial)
  | some expr =>
    obtain ⟨info, element, integer, childStart, sizeFinish, placeSource, elementShape, sizeSource, fillSource, _, _⟩ :=
      tyStmt_resize_children source
    let address := lowerPlace owner (lowerEnv env.mod env.vars results) before
    let count := lowerExpr size (lowerEnv env.mod env.vars results) address.2
    have addressGenerated := generated.lowerPlace owner (show lowerPlace owner _ before = address from rfl)
    have countGenerated := addressGenerated.lowerExpr size (show lowerExpr size _ address.2 = count from rfl)
    change ReplacementSitesAt (targets := targets) _ _ (lowerPlace owner >>= fun address => do
      let count ← lowerExpr size
      let filling ← (do pure (some (← lowerExpr expr)))
      emitEffect (.resize address count filling (some origin)))
    apply (placeChild placeSource generated).bind
    apply (sizeChild sizeSource addressGenerated).bind
    apply ReplacementSitesAt.bind
    · exact (fillChild expr rfl fillSource countGenerated).bind (ReplacementSitesAt.pure _ _ _)
    · exact ReplacementSitesAt.emitEffect _ (by intros; trivial)

end Goose.Lower.Validation

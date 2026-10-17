import Goose.Lower.Validation.ReplacementSourceSitesStatements
import Goose.Lower.Validation.SourceReadable

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem replacementSites_rebind_source {env output : Core.TEnv} {results : List Ty}
    {slot : VarId} {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.rebind slot expr origin) start = .ok (output, finish))
    (sourceTypes : SourceReadableEnvironment env)
    (exprChild : ReplacementSitesExprChild env results expr)
    (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.rebind slot expr origin)) := by
  obtain ⟨localVar, childType, row, _, reference, mutable, childSource, passable, _⟩ := tyStmt_rebind_children source
  change ReplacementSitesAt _ _ (lowerExpr expr >>= fun value => do
    let value ← coerceSlot slot value origin
    let address ← emitDef (.slotAddr slot)
    emitEffect (.store address value (some origin)))
  apply (exprChild childSource generated).bind
  apply (ReplacementSitesAt.coerceSlot _ _ _ _ _).bind
  apply (ReplacementSitesAt.emitDef _ (by intros; trivial)).bind
  exact ReplacementSitesAt.emitEffect _ (by intros; trivial)

end Goose.Lower.Validation

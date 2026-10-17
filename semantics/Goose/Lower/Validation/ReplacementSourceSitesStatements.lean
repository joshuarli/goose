import Goose.Lower.Validation.ReplacementSourceSitesOutputs
import Goose.Lower.Validation.ReplacementSourceSitesCoercions
import Goose.Lower.Validation.SourceStatementTypingStorage

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem replacementSites_assign_source {env output : Core.TEnv} {results : List Ty}
    {place : Place} {expr : Expr} {origin : OriginId}
    {scope start finish : Nat} (source : Core.tyStmt env scope (.assign place expr origin) start = .ok (output, finish))
    (placeChild : ReplacementSitesPlaceChild env results place) (exprChild : ReplacementSitesExprChild env results expr)
    (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.assign place expr origin)) := by
  obtain ⟨info, childStart, placeSource, childSource, copyable, writable, _⟩ := tyStmt_assign_children source
  let address := lowerPlace place (lowerEnv env.mod env.vars results) before
  have addressGenerated := generated.lowerPlace place (show lowerPlace place _ before = address from rfl)
  change ReplacementSitesAt _ _ (lowerPlace place >>= fun address => do
    let value ← lowerExpr expr
    emitEffect (.store address value (some origin)))
  apply (placeChild placeSource generated).bind
  apply (exprChild childSource addressGenerated).bind
  exact ReplacementSitesAt.emitEffect _ (by intros; trivial)

theorem replacementSites_append_source {env output : Core.TEnv} {results : List Ty}
    {owner : Place} {view : View} {origin : OriginId}
    {scope start finish : Nat} (source : Core.tyStmt env scope (.append owner view origin) start = .ok (output, finish))
    (placeChild : ReplacementSitesPlaceChild env results owner) (viewChild : ReplacementSitesViewChild env results view)
    (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.append owner view origin)) := by
  obtain ⟨info, element, writable, childStart, placeSource, elementShape, viewSource, _, _⟩ := tyStmt_append_children source
  let address := lowerPlace owner (lowerEnv env.mod env.vars results) before
  have addressGenerated := generated.lowerPlace owner (show lowerPlace owner _ before = address from rfl)
  change ReplacementSitesAt _ _ (lowerPlace owner >>= fun address => do
    let value ← lowerView view
    emitEffect (.append address value (some origin)))
  apply (placeChild placeSource generated).bind
  apply (viewChild viewSource addressGenerated).bind
  exact ReplacementSitesAt.emitEffect _ (by intros; trivial)

theorem replacementSites_clear_source {env output : Core.TEnv} {results : List Ty}
    {owner : Place} {origin : OriginId}
    {scope start finish : Nat} (source : Core.tyStmt env scope (.clear owner origin) start = .ok (output, finish))
    (placeChild : ReplacementSitesPlaceChild env results owner)
    (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.clear owner origin)) := by
  obtain ⟨info, element, placeSource, elementShape, _, _⟩ := tyStmt_clear_children source
  change ReplacementSitesAt _ _ (lowerPlace owner >>= fun address => emitEffect (.clear address (some origin)))
  apply (placeChild placeSource generated).bind
  exact ReplacementSitesAt.emitEffect _ (by intros; trivial)

theorem replacementSites_popN_source {env output : Core.TEnv} {results : List Ty}
    {owner : Place} {count : Expr} {origin : OriginId}
    {scope start finish : Nat} (source : Core.tyStmt env scope (.popN owner count origin) start = .ok (output, finish))
    (placeChild : ReplacementSitesPlaceChild env results owner) (exprChild : ReplacementSitesExprChild env results count)
    (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.popN owner count origin)) := by
  obtain ⟨info, element, integer, childStart, placeSource, elementShape, countSource, _, _⟩ := tyStmt_popN_children source
  let address := lowerPlace owner (lowerEnv env.mod env.vars results) before
  have addressGenerated := generated.lowerPlace owner (show lowerPlace owner _ before = address from rfl)
  change ReplacementSitesAt _ _ (lowerPlace owner >>= fun address => do
    let value ← lowerExpr count
    emitEffect (.popN address value (some origin)))
  apply (placeChild placeSource generated).bind
  apply (exprChild countSource addressGenerated).bind
  exact ReplacementSitesAt.emitEffect _ (by intros; trivial)

theorem replacementSites_assignOp_source {env output : Core.TEnv} {results : List Ty}
    {place : Place} {expr : Expr} {operation : BinOp} {origin : OriginId}
    {scope start finish : Nat} (source : Core.tyStmt env scope (.assignOp operation place expr origin) start = .ok (output, finish))
    (placeChild : ReplacementSitesPlaceChild env results place) (exprChild : ReplacementSitesExprChild env results expr)
    (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (lowerEnv env.mod env.vars results) before (lowerStmt loop (.assignOp operation place expr origin)) := by
  obtain ⟨info, integer, childStart, placeSource, integerShape, childSource, writable, _⟩ := tyStmt_assignOp_children source
  let le := lowerEnv env.mod env.vars results
  let address := lowerPlace place le before
  let loaded := emitDef (.load address.1) le address.2
  let rhs := lowerExpr expr le loaded.2
  let kind := intTyOf loaded.1 le rhs.2
  let binary := emitDef (.bin operation kind.1 loaded.1 rhs.1 (some origin)) le kind.2
  have addressGenerated := generated.lowerPlace place (show lowerPlace place le before = address from rfl)
  have loadedGenerated := addressGenerated.emitDef (.load address.1) (show emitDef _ le address.2 = loaded from rfl)
  change ReplacementSitesAt _ _ (lowerPlace place >>= fun address => do
    let old ← emitDef (.load address)
    let value ← lowerExpr expr
    let result ← emitDef (.bin operation (← intTyOf old) old value (some origin))
    emitEffect (.store address result (some origin)))
  apply (placeChild placeSource generated).bind
  apply ReplacementSitesAt.bind
  · exact ReplacementSitesAt.emitDef _ (by intros; trivial)
  · apply (exprChild childSource loadedGenerated).bind
    apply (ReplacementSitesAt.intTyOf _ _ _).bind
    apply (ReplacementSitesAt.emitDef _ (by intros; trivial)).bind
    exact ReplacementSitesAt.emitEffect _ (by intros; trivial)

#print axioms replacementSites_assign_source
#print axioms replacementSites_assignOp_source
#print axioms replacementSites_append_source
#print axioms replacementSites_popN_source
#print axioms replacementSites_clear_source

end Goose.Lower.Validation

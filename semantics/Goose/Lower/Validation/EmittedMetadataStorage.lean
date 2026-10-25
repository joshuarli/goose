import Goose.Lower.Validation.EmittedMetadataCollections
import Goose.Lower.Validation.SourceStatementTypingStorage
import Goose.Lower.Validation.ExpressionTypingGenerated

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem metadata_owner_append_shape {type element : Ty} (shape : type.ownerElem? = some element) :
    type = .grow element ∨ type = .growshrink element ∨ ∃ capacity, type = .limited element capacity := by
  cases type <;> simp_all [Ty.ownerElem?]

theorem metadata_source_assign {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : EmittedMetadataSourcePlace env results place) (exprChild : EmittedMetadataSourceExpression env results expr) :
    EmittedMetadataSourceStatement env results scope (.assign place expr origin) := by
  intro agreement output start finish source loop before result after generated loopBounds loopTypes run checked
  obtain ⟨info, childStart, placeSource, exprSource, _, _, _⟩ := tyStmt_assign_children source
  change (do let address ← lowerPlace place; let value ← lowerExpr expr; emitEffect (.store address value (some origin)))
    (lowerEnv env.mod env.vars results) before = (result, after) at run
  obtain ⟨address, placeState, placeRun, value, valueState, valueRun, emitted⟩ := by simpa only [bind_eq] using run
  have placeMetadata := placeChild agreement placeSource before address placeState generated trivial trivial placeRun checked
  have placeGenerated := generated.lowerPlace place placeRun
  have valueMetadata := exprChild agreement exprSource placeState value valueState placeGenerated trivial trivial valueRun placeMetadata
  have finished := valueMetadata.emitEffect (.store address value (some origin)) (by
    intro live
    have ownerLive := (dead_lowerExpr expr).live_before valueRun live
    obtain ⟨mu, ownerRow⟩ := lowerPlace_generated_typed place placeSource placeRun ownerLive generated
    exact .store ((types_lowerExpr expr _ placeState value valueState valueRun) _ _ ownerRow)
      (lowerExpr_generated_typed expr exprSource valueRun live placeGenerated))
  simpa only [emitted] using finished

theorem metadata_source_clear {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (origin : OriginId) (child : EmittedMetadataSourcePlace env results place) :
    EmittedMetadataSourceStatement env results scope (.clear place origin) := by
  intro agreement output start finish source loop before result after generated loopBounds loopTypes run checked
  obtain ⟨info, element, placeSource, ownerType, _, _⟩ := tyStmt_clear_children source
  change (do let address ← lowerPlace place; emitEffect (.clear address (some origin)))
    (lowerEnv env.mod env.vars results) before = (result, after) at run
  obtain ⟨address, placeState, placeRun, emitted⟩ := bind_eq.mp run
  have placeMetadata := child agreement placeSource before address placeState generated trivial trivial placeRun checked
  have finished := placeMetadata.emitEffect (.clear address (some origin)) (by
    intro live
    obtain ⟨mu, ownerRow⟩ := lowerPlace_generated_typed place placeSource placeRun live generated
    exact .clear ownerRow ownerType)
  simpa only [emitted] using finished

theorem metadata_source_append {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (view : View) (origin : OriginId)
    (placeChild : EmittedMetadataSourcePlace env results place) (viewChild : EmittedMetadataSourceView env results view) :
    EmittedMetadataSourceStatement env results scope (.append place view origin) := by
  intro agreement output start finish source loop before result after generated loopBounds loopTypes run checked
  obtain ⟨info, element, writable, childStart, placeSource, ownerType, viewSource, _, _⟩ := tyStmt_append_children source
  change (do let address ← lowerPlace place; let value ← lowerView view; emitEffect (.append address value (some origin)))
    (lowerEnv env.mod env.vars results) before = (result, after) at run
  obtain ⟨address, placeState, placeRun, value, viewState, viewRun, emitted⟩ := by simpa only [bind_eq] using run
  have placeMetadata := placeChild agreement placeSource before address placeState generated trivial trivial placeRun checked
  have placeGenerated := generated.lowerPlace place placeRun
  have viewMetadata := viewChild agreement viewSource placeState value viewState placeGenerated trivial trivial viewRun placeMetadata
  have finished := viewMetadata.emitEffect (.append address value (some origin)) (by
    intro live
    have ownerLive := (dead_lowerView view).live_before viewRun live
    obtain ⟨mu, ownerRow⟩ := lowerPlace_generated_typed place placeSource placeRun ownerLive generated
    obtain ⟨viewMu, viewRow⟩ := lowerView_generated_typed view viewSource viewRun live placeGenerated
    exact .append ((types_lowerView view _ placeState value viewState viewRun) _ _ ownerRow)
      (metadata_owner_append_shape ownerType) viewRow)
  simpa only [emitted] using finished

theorem metadata_source_popN {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : EmittedMetadataSourcePlace env results place) (exprChild : EmittedMetadataSourceExpression env results expr) :
    EmittedMetadataSourceStatement env results scope (.popN place expr origin) := by
  intro agreement output start finish source loop before result after generated loopBounds loopTypes run checked
  obtain ⟨info, element, integer, childStart, placeSource, ownerType, exprSource, _, _⟩ := tyStmt_popN_children source
  change (do let address ← lowerPlace place; let value ← lowerExpr expr; emitEffect (.popN address value (some origin)))
    (lowerEnv env.mod env.vars results) before = (result, after) at run
  obtain ⟨address, placeState, placeRun, value, valueState, valueRun, emitted⟩ := by simpa only [bind_eq] using run
  have placeMetadata := placeChild agreement placeSource before address placeState generated trivial trivial placeRun checked
  have placeGenerated := generated.lowerPlace place placeRun
  have valueMetadata := exprChild agreement exprSource placeState value valueState placeGenerated trivial trivial valueRun placeMetadata
  have finished := valueMetadata.emitEffect (.popN address value (some origin)) (by
    intro live
    have ownerLive := (dead_lowerExpr expr).live_before valueRun live
    obtain ⟨mu, ownerRow⟩ := lowerPlace_generated_typed place placeSource placeRun ownerLive generated
    exact .popN ((types_lowerExpr expr _ placeState value valueState valueRun) _ _ ownerRow) ownerType
      (lowerExpr_generated_typed expr exprSource valueRun live placeGenerated))
  simpa only [emitted] using finished

end Goose.Lower.Validation

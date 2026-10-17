import Goose.Lower.Validation.EmittedMetadataStorage

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem metadata_source_assignWhole {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : EmittedMetadataSourcePlace env results place) (exprChild : EmittedMetadataSourceExpression env results expr) :
    EmittedMetadataSourceStatement env results scope (.assignWhole place expr origin) := by
  intro agreement output start finish source loop before result after generated loopBounds loopTypes run checked
  obtain ⟨info, element, childStart, placeSource, ownerType, exprSource, _, _, _⟩ := tyStmt_assignWhole_children source
  let le := lowerEnv env.mod env.vars results
  change (do
    let address ← lowerPlace place
    emitEffect (.clear address (some origin))
    let value ← lowerExpr expr
    emitEffect (.replace address value (some origin))) le before = (result, after) at run
  obtain ⟨address, placeState, placeRun, ignored, clearState, clearRun, value, valueState, valueRun, emitted⟩ := by
    simpa only [bind_eq] using run
  have placeMetadata := placeChild agreement placeSource before address placeState generated trivial trivial placeRun checked
  have placeGenerated := generated.lowerPlace place placeRun
  have ownerElement : info.ty.ownerElem? = some element := by rcases ownerType with h | h <;> simp [h, Ty.ownerElem?]
  have clearMetadata := placeMetadata.emitEffect (.clear address (some origin)) (by
    intro live
    obtain ⟨mu, row⟩ := lowerPlace_generated_typed place placeSource placeRun live generated
    exact .clear row ownerElement)
  rw [clearRun] at clearMetadata
  have clearGenerated := placeGenerated.emitEffect (.clear address (some origin)) clearRun
  have valueMetadata := exprChild agreement exprSource clearState value valueState clearGenerated trivial trivial valueRun clearMetadata
  have finished := valueMetadata.emitEffect (.replace address value (some origin)) (by
    intro live
    have clearLive := (dead_lowerExpr expr).live_before valueRun live
    have ownerLive := (dead_emitEffect (.clear address (some origin))).live_before clearRun clearLive
    obtain ⟨mu, ownerRow⟩ := lowerPlace_generated_typed place placeSource placeRun ownerLive generated
    have kept := (types_lowerExpr expr le clearState value valueState valueRun) _ _
      ((types_emitEffect (.clear address (some origin)) le placeState ignored clearState clearRun) _ _ ownerRow)
    have shape : (∃ element, info.ty = .grow element) ∨ ∃ element, info.ty = .growshrink element :=
      ownerType.elim (fun h => Or.inl ⟨element, h⟩) (fun h => Or.inr ⟨element, h⟩)
    exact .replace kept shape (lowerExpr_generated_typed expr exprSource valueRun live clearGenerated))
  dsimp only [le] at emitted
  simpa only [emitted] using finished

theorem metadata_source_resize {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (place : Place) (size : Expr) (fill : Option Expr) (origin : OriginId)
    (placeChild : EmittedMetadataSourcePlace env results place) (sizeChild : EmittedMetadataSourceExpression env results size)
    (fillChild : ∀ expr, fill = some expr → EmittedMetadataSourceExpression env results expr) :
    EmittedMetadataSourceStatement env results scope (.resize place size fill origin) := by
  intro agreement output start finish source loop before result after generated loopBounds loopTypes run checked
  obtain ⟨info, element, integer, childStart, sizeFinish, placeSource, ownerType, sizeSource, fillSource, _, _⟩ :=
    tyStmt_resize_children source
  let le := lowerEnv env.mod env.vars results
  cases fill with
  | none =>
    change (do
      let address ← lowerPlace place
      let count ← lowerExpr size
      let fillValue ← pure none
      emitEffect (.resize address count fillValue (some origin))) le before = (result, after) at run
    obtain ⟨address, placeState, placeRun, count, countState, countRun, fillValue, fillState, fillRun, emitted⟩ := by
      simpa only [bind_eq] using run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj fillRun
    have placeMetadata := placeChild agreement placeSource before address placeState generated trivial trivial placeRun checked
    have placeGenerated := generated.lowerPlace place placeRun
    have countMetadata := sizeChild agreement sizeSource placeState count countState placeGenerated trivial trivial countRun placeMetadata
    have finished := countMetadata.emitEffect (.resize address count none (some origin)) (by
      intro live
      have ownerLive := (dead_lowerExpr size).live_before countRun live
      obtain ⟨mu, ownerRow⟩ := lowerPlace_generated_typed place placeSource placeRun ownerLive generated
      exact .resize ((types_lowerExpr size le placeState count countState countRun) _ _ ownerRow) ownerType
        (lowerExpr_generated_typed size sizeSource countRun live placeGenerated) (by intro value same; cases same))
    dsimp only [le] at emitted
    simpa only [emitted] using finished
  | some expr =>
    change (do
      let address ← lowerPlace place
      let count ← lowerExpr size
      let fillValue ← (do let value ← lowerExpr expr; pure (some value))
      emitEffect (.resize address count fillValue (some origin))) le before = (result, after) at run
    obtain ⟨address, placeState, placeRun, count, countState, countRun, fillValue, fillState, fillRun, emitted⟩ := by
      simpa only [bind_eq] using run
    obtain ⟨value, valueState, valueRun, pureRun⟩ := fillRun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pureRun
    have placeMetadata := placeChild agreement placeSource before address placeState generated trivial trivial placeRun checked
    have placeGenerated := generated.lowerPlace place placeRun
    have countMetadata := sizeChild agreement sizeSource placeState count countState placeGenerated trivial trivial countRun placeMetadata
    have countGenerated := placeGenerated.lowerExpr size countRun
    have valueMetadata := fillChild expr rfl agreement fillSource countState value valueState countGenerated trivial trivial valueRun countMetadata
    have finished := valueMetadata.emitEffect (.resize address count (some value) (some origin)) (by
      intro live
      have countLive := (dead_lowerExpr expr).live_before valueRun live
      have ownerLive := (dead_lowerExpr size).live_before countRun countLive
      obtain ⟨mu, ownerRow⟩ := lowerPlace_generated_typed place placeSource placeRun ownerLive generated
      have ownerKept := (types_lowerExpr expr le countState value valueState valueRun) _ _
        ((types_lowerExpr size le placeState count countState countRun) _ _ ownerRow)
      have countKept := (types_lowerExpr expr le countState value valueState valueRun) _ _
        (lowerExpr_generated_typed size sizeSource countRun countLive placeGenerated)
      exact .resize ownerKept ownerType countKept (by
        intro candidate same
        cases Option.some.inj same
        exact lowerExpr_generated_typed expr fillSource valueRun live countGenerated))
    dsimp only [le] at emitted
    simpa only [emitted] using finished


theorem metadata_source_assignOp {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (op : BinOp) (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : EmittedMetadataSourcePlace env results place) (exprChild : EmittedMetadataSourceExpression env results expr) :
    EmittedMetadataSourceStatement env results scope (.assignOp op place expr origin) := by
  intro agreement output start finish source loop before result after generated loopBounds loopTypes run checked
  obtain ⟨info, integer, childStart, placeSource, infoType, exprSource, _, _⟩ := tyStmt_assignOp_children source
  let le := lowerEnv env.mod env.vars results
  change (do
    let address ← lowerPlace place
    let old ← emitDef (.load address)
    let rhs ← lowerExpr expr
    let hint ← intTyOf old
    let value ← emitDef (.bin op hint old rhs (some origin))
    emitEffect (.store address value (some origin))) le before = (result, after) at run
  obtain ⟨address, placeState, placeRun, old, loadState, loadRun, rhs, rhsState, rhsRun,
    hint, observed, intRead, value, valueState, valueRun, emitted⟩ := by simpa only [bind_eq] using run
  have same := intTyOf_eq intRead
  subst observed
  have placeMetadata := placeChild agreement placeSource before address placeState generated trivial trivial placeRun checked
  have placeGenerated := generated.lowerPlace place placeRun
  have loadMetadata := placeMetadata.emitDef (.load address)
  rw [loadRun] at loadMetadata
  have loadGenerated := placeGenerated.emitDef (.load address) loadRun
  have rhsMetadata := exprChild agreement exprSource loadState rhs rhsState loadGenerated trivial trivial rhsRun loadMetadata
  have valueMetadata := rhsMetadata.emitDef (.bin op hint old rhs (some origin))
  rw [valueRun] at valueMetadata
  have finished := valueMetadata.emitEffect (.store address value (some origin)) (by
    intro live
    have rhsLive := (dead_emitDef (.bin op hint old rhs (some origin))).live_before valueRun live
    have loadLive := (dead_lowerExpr expr).live_before rhsRun rhsLive
    have ownerLive := (dead_emitDef (.load address)).live_before loadRun loadLive
    obtain ⟨mu, ownerRow⟩ := lowerPlace_generated_typed place placeSource placeRun ownerLive generated
    have ownerInteger : placeState.vals[address]? = some (some (.data (.ref mu (.int integer)))) := by simpa only [infoType] using ownerRow
    have loadSuccess : (Op.load address).resultTy (tyEnv le placeState) = .ok (.data (.int integer)) := by
      simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, ownerInteger,
        pure, Except.pure, bind, Except.bind]
    cases current : placeState.cur with
    | none => simp [current] at ownerLive
    | some block =>
      have loadedRow : (emitDef (.load address) le placeState).2.vals[(emitDef (.load address) le placeState).1]? =
          some (some (.data (.int integer))) := (emitDef_recorded current loadSuccess).2.2.1
      rw [loadRun] at loadedRow
      have oldRow := (types_lowerExpr expr le loadState rhs rhsState rhsRun) _ _ loadedRow
      have hintEq : hint = integer := by
        have both := (intTyOf_recorded (le := le) oldRow).symm.trans intRead
        exact (congrArg Prod.fst both).symm
      have rhsRow := lowerExpr_generated_typed expr exprSource rhsRun rhsLive loadGenerated
      have operationSuccess : (Op.bin op hint old rhs (some origin)).resultTy (tyEnv le rhsState) = .ok (.data (.int integer)) := by
        simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, oldRow, rhsRow, hintEq,
          pure, Except.pure, bind, Except.bind]
      cases computedCurrent : rhsState.cur with
      | none => simp [computedCurrent] at rhsLive
      | some computedBlock =>
        have computedRow : (emitDef (.bin op hint old rhs (some origin)) le rhsState).2.vals[
            (emitDef (.bin op hint old rhs (some origin)) le rhsState).1]? = some (some (.data (.int integer))) :=
          (emitDef_recorded computedCurrent operationSuccess).2.2.1
        rw [valueRun] at computedRow
        have kept := (types_emitDef (.bin op hint old rhs (some origin)) le rhsState value valueState valueRun) _ _
          ((types_lowerExpr expr le loadState rhs rhsState rhsRun) _ _ ((types_emitDef (.load address) le placeState old loadState loadRun) _ _ ownerInteger))
        exact .store kept computedRow)
  dsimp only [le] at emitted
  simpa only [emitted] using finished

end Goose.Lower.Validation

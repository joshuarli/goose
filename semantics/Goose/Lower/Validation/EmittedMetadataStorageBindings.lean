import Goose.Lower.Validation.EmittedMetadataStorage
import Goose.Lower.Validation.EmittedMetadataCoercions

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem metadata_source_let {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (slot : SlotId) (expr : Expr) (origin : OriginId) (child : EmittedMetadataSourceExpression env results expr) :
    EmittedMetadataSourceStatement env results scope (.letS slot expr origin) := by
  intro agreement output start finish source loop before result after generated loopBounds loopTypes run checked
  obtain ⟨localVar, type, childStart, declared, childSource, permission, _⟩ := tyStmt_let_children source
  have localRow := (declare_ok _ _ _ _ _ declared).2.1
  have slotAt : (lowerEnv env.mod env.vars results).slots[slot]? =
      some ⟨localVar.ty, localVar.kind, localVar.scope, slot⟩ := by
    simp [lowerEnv, Array.getElem?_mapIdx, localRow]
  change (do let value ← lowerExpr expr; let coerced ← coerceSlot slot value origin; emitEffect (.slotInit slot coerced (some origin)))
    (lowerEnv env.mod env.vars results) before = (result, after) at run
  obtain ⟨value, valueState, valueRun, coerced, coercedState, coercedRun, emitted⟩ := by simpa only [bind_eq] using run
  have valueMetadata := child agreement childSource before value valueState generated trivial trivial valueRun checked
  have valueGenerated := generated.lowerExpr expr valueRun
  have coercedMetadata := (EmittedMetadataAction.coerceSlot _ none slot value origin).metadata
    valueState coerced coercedState valueGenerated trivial trivial coercedRun valueMetadata
  have finished := coercedMetadata.emitEffect (.slotInit slot coerced (some origin)) (by
    intro live
    have inputLive := (metadata_dead_coerceSlot slot value origin).live_before coercedRun live
    have valueRow := lowerExpr_generated_typed expr childSource valueRun inputLive generated
    cases current : valueState.cur with
    | none => simp [current] at inputLive
    | some block =>
      have targetRow := metadata_coerceSlot_typed slotAt valueRow permission current origin
      rw [coercedRun] at targetRow
      exact .slotInit slotAt targetRow)
  simpa only [emitted] using finished

theorem metadata_source_rebind {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (slot : SlotId) (expr : Expr) (origin : OriginId) (child : EmittedMetadataSourceExpression env results expr) :
    EmittedMetadataSourceStatement env results scope (.rebind slot expr origin) := by
  intro agreement output start finish source loop before result after generated loopBounds loopTypes run checked
  obtain ⟨localVar, type, localRow, _, _, _, childSource, permission, _⟩ := tyStmt_rebind_children source
  let le := lowerEnv env.mod env.vars results
  have slotAt : le.slots[slot]? = some ⟨localVar.ty, localVar.kind, localVar.scope, slot⟩ := by
    simp [le, lowerEnv, Array.getElem?_mapIdx, localRow]
  change (do
    let value ← lowerExpr expr
    let coerced ← coerceSlot slot value origin
    let address ← emitDef (.slotAddr slot)
    emitEffect (.store address coerced (some origin))) le before = (result, after) at run
  obtain ⟨value, valueState, valueRun, coerced, coercedState, coercedRun,
    address, addressState, addressRun, emitted⟩ := by simpa only [bind_eq] using run
  have valueMetadata := child agreement childSource before value valueState generated trivial trivial valueRun checked
  have valueGenerated := generated.lowerExpr expr valueRun
  have coercedMetadata := (EmittedMetadataAction.coerceSlot le none slot value origin).metadata
    valueState coerced coercedState valueGenerated trivial trivial coercedRun valueMetadata
  have addressMetadata := coercedMetadata.emitDef (.slotAddr slot)
  rw [addressRun] at addressMetadata
  have finished := addressMetadata.emitEffect (.store address coerced (some origin)) (by
    intro live
    have coercedLive := (dead_emitDef (.slotAddr slot)).live_before addressRun live
    have valueLive := (metadata_dead_coerceSlot slot value origin).live_before coercedRun coercedLive
    have valueRow := lowerExpr_generated_typed expr childSource valueRun valueLive generated
    cases current : valueState.cur with
    | none => simp [current] at valueLive
    | some block =>
      have coercedRow := metadata_coerceSlot_typed slotAt valueRow permission current origin
      rw [coercedRun] at coercedRow
      have ownerResult : ∃ mu, (Op.slotAddr slot).resultTy (tyEnv le coercedState) = .ok (.data (.ref mu localVar.ty)) := by
        simp only [Op.resultTy, tyEnv, slotAt]
        exact ⟨_, rfl⟩
      obtain ⟨mu, ownerResult⟩ := ownerResult
      cases ownerCurrent : coercedState.cur with
      | none => simp [ownerCurrent] at coercedLive
      | some ownerBlock =>
        have ownerRow : (emitDef (.slotAddr slot) le coercedState).2.vals[(emitDef (.slotAddr slot) le coercedState).1]? =
            some (some (.data (.ref mu localVar.ty))) := (emitDef_recorded ownerCurrent ownerResult).2.2.1
        rw [addressRun] at ownerRow
        exact .store ownerRow ((types_emitDef (.slotAddr slot) le coercedState address addressState addressRun) _ _ coercedRow))
  simpa only [emitted] using finished

end Goose.Lower.Validation

import Goose.Lower.Validation.EmittedTypingSourceActions
import Goose.Lower.Validation.EmittedTypingMutationStatements
import Goose.Lower.Validation.SourceStatementTypingStorage
import Goose.Lower.Validation.EmittedTypingPlaceActions

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_source_let {env output : Core.TEnv} {results : List Ty}
    {slot : SlotId} {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.letS slot expr origin) start = .ok (output, finish))
    (child : EmittedSourceExpression env results expr) {initial before : LS}
    (loop : Option LoopCtx) (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before)
    (targets : LoopBuilderTargets loop before) :
    let after := (lowerStmt loop (.letS slot expr origin) (lowerEnv env.mod env.vars results) before).2
    EmittedBuilder (lowerEnv env.mod env.vars results) initial after ∧ GeneratedBuilderState after := by
  obtain ⟨localVar, type, childStart, declared, childSource, passable, _⟩ := tyStmt_let_children source
  exact ⟨emitted_checked_lowerStmt_let loop slot expr origin (child childSource generated builder),
    generated.lowerStmt loop _ targets rfl⟩

theorem emitted_source_assign {env output : Core.TEnv} {results : List Ty}
    {place : Place} {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assign place expr origin) start = .ok (output, finish))
    (placeChild : EmittedSourcePlace env results place) (exprChild : EmittedSourceExpression env results expr)
    {initial before : LS} (loop : Option LoopCtx) (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before)
    (targets : LoopBuilderTargets loop before) :
    let after := (lowerStmt loop (.assign place expr origin) (lowerEnv env.mod env.vars results) before).2
    EmittedBuilder (lowerEnv env.mod env.vars results) initial after ∧ GeneratedBuilderState after := by
  obtain ⟨info, childStart, placeSource, exprSource, _, _, _⟩ := tyStmt_assign_children source
  have placeBuilder := placeChild placeSource generated builder
  have placeGenerated : GeneratedBuilderState (lowerPlace place (lowerEnv env.mod env.vars results) before).2 :=
    generated.lowerPlace place rfl
  have valueBuilder := exprChild exprSource placeGenerated placeBuilder
  exact ⟨emitted_checked_lowerStmt_assign loop place expr origin valueBuilder,
    generated.lowerStmt loop _ targets rfl⟩

theorem emitted_source_clear {env output : Core.TEnv} {results : List Ty}
    {place : Place} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.clear place origin) start = .ok (output, finish))
    (child : EmittedSourcePlace env results place) {initial before : LS}
    (loop : Option LoopCtx) (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before)
    (targets : LoopBuilderTargets loop before) :
    let after := (lowerStmt loop (.clear place origin) (lowerEnv env.mod env.vars results) before).2
    EmittedBuilder (lowerEnv env.mod env.vars results) initial after ∧ GeneratedBuilderState after := by
  obtain ⟨info, element, childSource, _, _, _⟩ := tyStmt_clear_children source
  exact ⟨emitted_checked_lowerStmt_clear loop place origin (child childSource generated builder),
    generated.lowerStmt loop _ targets rfl⟩

theorem emitted_source_append {env output : Core.TEnv} {results : List Ty}
    {place : Place} {view : View} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.append place view origin) start = .ok (output, finish))
    (placeChild : EmittedSourcePlace env results place) (viewChild : EmittedSourceView env results view)
    {initial before : LS} (loop : Option LoopCtx) (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before)
    (targets : LoopBuilderTargets loop before) :
    let after := (lowerStmt loop (.append place view origin) (lowerEnv env.mod env.vars results) before).2
    EmittedBuilder (lowerEnv env.mod env.vars results) initial after ∧ GeneratedBuilderState after := by
  obtain ⟨info, element, writable, childStart, placeSource, _, viewSource, _, _⟩ := tyStmt_append_children source
  have placeBuilder := placeChild placeSource generated builder
  have placeGenerated : GeneratedBuilderState (lowerPlace place (lowerEnv env.mod env.vars results) before).2 :=
    generated.lowerPlace place rfl
  have viewBuilder := viewChild viewSource placeGenerated placeBuilder
  exact ⟨emitted_checked_lowerStmt_append loop place view origin viewBuilder,
    generated.lowerStmt loop _ targets rfl⟩

theorem emitted_source_popN {env output : Core.TEnv} {results : List Ty}
    {place : Place} {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.popN place expr origin) start = .ok (output, finish))
    (placeChild : EmittedSourcePlace env results place) (exprChild : EmittedSourceExpression env results expr)
    {initial before : LS} (loop : Option LoopCtx) (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before)
    (targets : LoopBuilderTargets loop before) :
    let after := (lowerStmt loop (.popN place expr origin) (lowerEnv env.mod env.vars results) before).2
    EmittedBuilder (lowerEnv env.mod env.vars results) initial after ∧ GeneratedBuilderState after := by
  obtain ⟨info, element, integer, childStart, placeSource, _, exprSource, _, _⟩ := tyStmt_popN_children source
  have placeBuilder := placeChild placeSource generated builder
  have placeGenerated : GeneratedBuilderState (lowerPlace place (lowerEnv env.mod env.vars results) before).2 :=
    generated.lowerPlace place rfl
  have valueBuilder := exprChild exprSource placeGenerated placeBuilder
  exact ⟨emitted_checked_lowerStmt_popN loop place expr origin valueBuilder,
    generated.lowerStmt loop _ targets rfl⟩

theorem emitted_source_rebind {env output : Core.TEnv} {results : List Ty}
    {slot : SlotId} {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.rebind slot expr origin) start = .ok (output, finish))
    (child : EmittedSourceExpression env results expr) {initial before : LS}
    (loop : Option LoopCtx) (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before)
    (targets : LoopBuilderTargets loop before) :
    let after := (lowerStmt loop (.rebind slot expr origin) (lowerEnv env.mod env.vars results) before).2
    EmittedBuilder (lowerEnv env.mod env.vars results) initial after ∧ GeneratedBuilderState after := by
  obtain ⟨localVar, type, localRow, _, _, _, childSource, _, _⟩ := tyStmt_rebind_children source
  have slotRow : (lowerEnv env.mod env.vars results).slots[slot]? =
      some ⟨localVar.ty, localVar.kind, localVar.scope, slot⟩ := by
    simp [lowerEnv, Array.getElem?_mapIdx, localRow]
  exact ⟨emitted_checked_lowerStmt_rebind loop slot expr origin _ slotRow (child childSource generated builder),
    generated.lowerStmt loop _ targets rfl⟩

theorem emitted_source_assignOp {env output : Core.TEnv} {results : List Ty}
    {op : BinOp} {place : Place} {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assignOp op place expr origin) start = .ok (output, finish))
    (placeChild : EmittedSourcePlace env results place) (exprChild : EmittedSourceExpression env results expr)
    {initial before : LS} (loop : Option LoopCtx) (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before)
    (targets : LoopBuilderTargets loop before) :
    let after := (lowerStmt loop (.assignOp op place expr origin) (lowerEnv env.mod env.vars results) before).2
    EmittedBuilder (lowerEnv env.mod env.vars results) initial after ∧ GeneratedBuilderState after := by
  obtain ⟨info, integer, childStart, placeSource, infoType, exprSource, _, _⟩ := tyStmt_assignOp_children source
  let le := lowerEnv env.mod env.vars results
  let address := lowerPlace place le before
  let loaded := emitDef (.load address.1) le address.2
  let rhs := lowerExpr expr le loaded.2
  let operation := Op.bin op (intTyOf loaded.1 le rhs.2).1 loaded.1 rhs.1 (some origin)
  let computed := emitDef operation le rhs.2
  have addressTyped : ∀ active, address.2.cur = some active →
      ∃ mu, address.2.vals[address.1]? = some (some (.data (.ref mu (.int integer)))) := by
    intro active current
    obtain ⟨mu, row⟩ := (emitted_source_results env results).place place placeSource generated
      (show lowerPlace place (lowerEnv env.mod env.vars results) before = address from rfl)
      (by change address.2.cur.isSome = true; rw [current]; rfl)
    exact ⟨mu, by simpa only [infoType] using row⟩
  have loadSuccess : address.2.cur.isSome = true →
      (Op.load address.1).resultTy (tyEnv le address.2) = .ok (.data (.int integer)) := by
    intro active
    cases current : address.2.cur with
    | none => simp [current] at active
    | some block =>
      obtain ⟨mu, row⟩ := addressTyped block current
      simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, row,
        pure, Except.pure, bind, Except.bind]
  have loadedBuilder : EmittedBuilder le initial loaded.2 := by
    apply (placeChild placeSource generated builder).emitDef (.load address.1)
    · intro active
      exact ⟨_, loadSuccess active⟩
    · intro active operand member
      have same : operand = address.1 := by simpa [Op.uses] using member
      subst operand
      exact value_lowerPlace place le before _ _ rfl active
  have loadedGenerated : GeneratedBuilderState loaded.2 :=
    (generated.lowerPlace place rfl).emitDef (.load address.1) rfl
  have rhsBuilder := exprChild exprSource loadedGenerated loadedBuilder
  have rows : rhs.2.cur.isSome = true →
      rhs.2.vals[loaded.1]? = some (some (.data (.int integer))) ∧
      rhs.2.vals[rhs.1]? = some (some (.data (.int integer))) := by
    intro active
    have loadedLive := (dead_lowerExpr expr).live_before rfl active
    have addressLive := (dead_emitDef (.load address.1)).live_before rfl loadedLive
    have oldTyped : loaded.2.vals[loaded.1]? = some (some (.data (.int integer))) := by
      cases current : address.2.cur with
      | none => simp [current] at addressLive
      | some block => exact (emitDef_recorded current (loadSuccess addressLive)).2.2.1
    exact ⟨(types_lowerExpr expr le loaded.2 _ _ rfl) _ _ oldTyped,
      (emitted_source_results env results).expression expr exprSource loadedGenerated rfl active⟩
  have operationSuccess : rhs.2.cur.isSome = true → operation.resultTy (tyEnv le rhs.2) = .ok (.data (.int integer)) := by
    intro active
    obtain ⟨oldTyped, rhsTyped⟩ := rows active
    have chosen : (intTyOf loaded.1 le rhs.2).1 = integer := congrArg Prod.fst (intTyOf_recorded oldTyped)
    dsimp only [operation]
    rw [chosen]
    dsimp only [le, address, loaded, rhs] at oldTyped rhsTyped ⊢
    simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, oldTyped, rhsTyped,
      pure, Except.pure, bind, Except.bind]
  have computedBuilder := rhsBuilder.emitDef operation (fun active => ⟨_, operationSuccess active⟩) (by
    intro active operand member
    obtain ⟨oldTyped, rhsTyped⟩ := rows active
    have either : operand = loaded.1 ∨ operand = rhs.1 := by simpa [operation, Op.uses] using member
    rcases either with rfl | rfl
    · exact (Array.getElem?_eq_some_iff.mp oldTyped).1
    · exact (Array.getElem?_eq_some_iff.mp rhsTyped).1)
  have finalBuilder := computedBuilder.emitEffect (.store address.1 computed.1 (some origin)) (by
    intro active operand member
    have either : operand = address.1 ∨ operand = computed.1 := by simpa [Effect.uses] using member
    rcases either with rfl | rfl
    · have rhsLive := (dead_emitDef operation).live_before rfl active
      have loadedLive := (dead_lowerExpr expr).live_before rfl rhsLive
      have addressLive := (dead_emitDef (.load address.1)).live_before rfl loadedLive
      have bound := value_lowerPlace place le before _ _ rfl addressLive
      exact Nat.lt_of_lt_of_le bound (Nat.le_trans (advB_emitDef (.load address.1) le address.2 _ _ rfl).vals
        (Nat.le_trans (advB_lowerExpr expr le loaded.2 _ _ rfl).vals (advB_emitDef operation le rhs.2 _ _ rfl).vals))
    · exact value_emitDef operation le rhs.2 _ _ rfl active)
  refine ⟨?_, generated.lowerStmt loop _ targets rfl⟩
  simpa only [lowerStmt, bind_run, intTyOf_state, le, address, loaded, rhs, operation, computed] using finalBuilder

theorem emitted_source_resize {env output : Core.TEnv} {results : List Ty}
    {place : Place} {size : Expr} {fill : Option Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.resize place size fill origin) start = .ok (output, finish))
    (placeChild : EmittedSourcePlace env results place) (sizeChild : EmittedSourceExpression env results size)
    (fillChild : ∀ expr, fill = some expr → EmittedSourceExpression env results expr)
    {initial before : LS} (loop : Option LoopCtx) (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before)
    (targets : LoopBuilderTargets loop before) :
    let after := (lowerStmt loop (.resize place size fill origin) (lowerEnv env.mod env.vars results) before).2
    EmittedBuilder (lowerEnv env.mod env.vars results) initial after ∧ GeneratedBuilderState after := by
  obtain ⟨info, element, integer, childStart, sizeFinish, placeSource, _, sizeSource, fillSource, _, _⟩ :=
    tyStmt_resize_children source
  have placeBuilder := placeChild placeSource generated builder
  have placeGenerated : GeneratedBuilderState (lowerPlace place (lowerEnv env.mod env.vars results) before).2 :=
    generated.lowerPlace place rfl
  have sizeBuilder := sizeChild sizeSource placeGenerated placeBuilder
  refine ⟨?_, generated.lowerStmt loop _ targets rfl⟩
  cases fill with
  | none => exact emitted_checked_lowerStmt_resize_none loop place size origin sizeBuilder
  | some expr =>
    have sizeGenerated : GeneratedBuilderState
        (lowerExpr size (lowerEnv env.mod env.vars results)
          (lowerPlace place (lowerEnv env.mod env.vars results) before).2).2 := placeGenerated.lowerExpr size rfl
    have fillBuilder := fillChild expr rfl fillSource sizeGenerated sizeBuilder
    exact emitted_checked_lowerStmt_resize_some loop place size expr origin fillBuilder

theorem emitted_source_assignWhole {env output : Core.TEnv} {results : List Ty}
    {place : Place} {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assignWhole place expr origin) start = .ok (output, finish))
    (placeChild : EmittedSourcePlace env results place) (exprChild : EmittedSourceExpression env results expr)
    {initial before : LS} (loop : Option LoopCtx) (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before)
    (targets : LoopBuilderTargets loop before) :
    let after := (lowerStmt loop (.assignWhole place expr origin) (lowerEnv env.mod env.vars results) before).2
    EmittedBuilder (lowerEnv env.mod env.vars results) initial after ∧ GeneratedBuilderState after := by
  obtain ⟨info, element, childStart, placeSource, _, exprSource, _, _, _⟩ := tyStmt_assignWhole_children source
  let le := lowerEnv env.mod env.vars results
  let address := lowerPlace place le before
  let cleared := emitEffect (.clear address.1 (some origin)) le address.2
  have placeBuilder := placeChild placeSource generated builder
  have clearBuilder := placeBuilder.emitEffect (.clear address.1 (some origin)) (by
    intro active operand member
    have same : operand = address.1 := by simpa [Effect.uses] using member
    subst operand
    exact value_lowerPlace place le before _ _ rfl active)
  have placeGenerated : GeneratedBuilderState address.2 := generated.lowerPlace place rfl
  have clearGenerated : GeneratedBuilderState cleared.2 := placeGenerated.emitEffect _ rfl
  have valueBuilder := exprChild exprSource clearGenerated clearBuilder
  exact ⟨emitted_checked_lowerStmt_assignWhole loop place expr origin valueBuilder,
    generated.lowerStmt loop _ targets rfl⟩

end Goose.Lower.Validation

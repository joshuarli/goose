import Goose.Lower.Validation.EmittedTypingSourceActions
import Goose.Lower.Validation.EmittedTypingMutationStatements
import Goose.Lower.Validation.SourceStatementTypingStorage

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

end Goose.Lower.Validation

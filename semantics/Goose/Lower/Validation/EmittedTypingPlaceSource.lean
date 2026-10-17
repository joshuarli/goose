import Goose.Lower.Validation.EmittedTypingSourceResults
import Goose.Lower.Validation.EmittedTypingAggregateCheckpoints
import Goose.Lower.Validation.ViewTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_checked_field_source {env : Core.TEnv} {results : List Ty}
    (outputs : EmittedSourceResults env results) {owner : Place} {index : Nat} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env (.field owner index) start = .ok (info, finish))
    (child : ∀ {info : PlaceInfo} {start finish : Nat},
      Core.tyPlace env owner start = .ok (info, finish) → ∀ {initial before : LS},
      GeneratedBuilderState before → EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial
        (lowerPlace owner (lowerEnv env.mod env.vars results) before).2)
    {initial before : LS} (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerPlace (.field owner index) (lowerEnv env.mod env.vars results) before).2 := by
  obtain ⟨ownerInfo, ownerFinish, ownerSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨field, fieldFinish, fieldSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨id, fields, descriptor, shape, table, payload, fieldRow⟩ := structField_descriptor fieldSource
  have tableLowered : (lowerEnv env.mod env.vars results).mod.structs[id]? = some descriptor := table
  have lowered := child ownerSource generated builder
  let value := lowerPlace owner (lowerEnv env.mod env.vars results) before
  apply lowered.emitDef (.fieldAddr value.1 index)
  · intro active
    obtain ⟨mu, typed⟩ := outputs.place owner ownerSource generated rfl active
    rw [shape] at typed
    exact ⟨.data (.ref (Mutability.ofKind field.binding) field.ty), by
      simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, value, typed,
        tableLowered, payload, fieldRow, pure, Except.pure, bind, Except.bind]⟩
  · intro active operand member
    have same : operand = value.1 := by simpa [Op.uses] using member
    subst operand
    obtain ⟨mu, typed⟩ := outputs.place owner ownerSource generated rfl active
    exact (Array.getElem?_eq_some_iff.mp typed).1

theorem emitted_checked_index_source {env : Core.TEnv} {results : List Ty}
    (outputs : EmittedSourceResults env results) {view : View} {index : Expr} {origin : OriginId}
    {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env (.elem view index origin) start = .ok (info, finish))
    (viewChild : ∀ {element : Ty} {writable : Bool} {start finish : Nat},
      Core.tyView env view start = .ok ((element, writable), finish) → ∀ {initial before : LS},
      GeneratedBuilderState before → EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial
        (lowerView view (lowerEnv env.mod env.vars results) before).2)
    (indexChild : ∀ {type : Ty} {start finish : Nat},
      Core.tyExpr env index start = .ok (type, finish) → ∀ {initial before : LS},
      GeneratedBuilderState before → EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial
        (lowerExpr index (lowerEnv env.mod env.vars results) before).2)
    {initial before : LS} (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerPlace (.elem view index origin) (lowerEnv env.mod env.vars results) before).2 := by
  obtain ⟨viewStart, viewFinish, indexFinish, writable, type, viewSource, indexSource⟩ :=
    tyPlace_elem_children source
  let viewValue := lowerView view (lowerEnv env.mod env.vars results) before
  let indexValue := lowerExpr index (lowerEnv env.mod env.vars results) viewValue.2
  have viewBuilder := viewChild viewSource generated builder
  have viewGenerated := generated.lowerView view (show lowerView view _ before = viewValue from rfl)
  have indexBuilder := indexChild indexSource viewGenerated viewBuilder
  have rows : indexValue.2.cur.isSome = true →
      ∃ mu, indexValue.2.vals[viewValue.1]? = some (some (.view mu info.ty)) ∧
        indexValue.2.vals[indexValue.1]? = some (some (.data (.int type))) := by
    intro active
    have viewLive := (dead_lowerExpr index).live_before rfl active
    obtain ⟨mu, typed⟩ := outputs.view view viewSource generated rfl viewLive
    exact ⟨mu, (types_lowerExpr index _ viewValue.2 _ _ rfl) _ _ typed,
      outputs.expression index indexSource viewGenerated rfl active⟩
  apply indexBuilder.emitDef (.indexChecked viewValue.1 indexValue.1 (some origin))
  · intro active
    obtain ⟨mu, viewTyped, indexTyped⟩ := rows active
    dsimp only [viewValue, indexValue] at viewTyped indexTyped ⊢
    exact ⟨.data (.ref mu info.ty), by
      simp [Op.resultTy, TyEnv.viewTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
        viewTyped, indexTyped, pure, Except.pure, bind, Except.bind]⟩
  · intro active operand member
    obtain ⟨mu, viewTyped, indexTyped⟩ := rows active
    have either : operand = viewValue.1 ∨ operand = indexValue.1 := by simpa [Op.uses] using member
    rcases either with rfl | rfl
    · exact (Array.getElem?_eq_some_iff.mp viewTyped).1
    · exact (Array.getElem?_eq_some_iff.mp indexTyped).1

end Goose.Lower.Validation

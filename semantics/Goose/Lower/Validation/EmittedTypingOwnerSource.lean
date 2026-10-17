import Goose.Lower.Validation.EmittedTypingSourceResults
import Goose.Lower.Validation.EmittedTypingAggregateCheckpoints
import Goose.Lower.Validation.ExpressionTypingScalarOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_checked_pop_source {env : Core.TEnv} {results : List Ty}
    (outputs : EmittedSourceResults env results) {owner : Place} {origin : OriginId} {type : Ty}
    {start finish : Nat} (source : Core.tyExpr env (.pop owner origin) start = .ok (type, finish))
    (child : ∀ {info : PlaceInfo} {start finish : Nat},
      Core.tyPlace env owner start = .ok (info, finish) → ∀ {initial before : LS},
      GeneratedBuilderState before → EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial
        (lowerPlace owner (lowerEnv env.mod env.vars results) before).2)
    {initial before : LS} (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerExpr (.pop owner origin) (lowerEnv env.mod env.vars results) before).2 := by
  obtain ⟨info, ownerStart, ownerFinish, ownerSource, element⟩ := tyExpr_pop_owner source
  have lowered := child ownerSource generated builder
  let value := lowerPlace owner (lowerEnv env.mod env.vars results) before
  apply lowered.emitDef (.pop value.1 (some origin))
  · intro active
    obtain ⟨mu, typed⟩ := outputs.place owner ownerSource generated rfl active
    exact ⟨.data type, by
      simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, value, typed, element,
        pure, Except.pure, bind, Except.bind]⟩
  · intro active operand member
    have same : operand = value.1 := by simpa [Op.uses] using member
    subst operand
    obtain ⟨mu, typed⟩ := outputs.place owner ownerSource generated rfl active
    exact (Array.getElem?_eq_some_iff.mp typed).1

theorem emitted_checked_push_source {env : Core.TEnv} {results : List Ty}
    (outputs : EmittedSourceResults env results) {owner : Place} {expr : Expr}
    {origin : Option OriginId} {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.push owner expr origin) start = .ok (type, finish))
    (placeChild : ∀ {info : PlaceInfo} {start finish : Nat},
      Core.tyPlace env owner start = .ok (info, finish) → ∀ {initial before : LS},
      GeneratedBuilderState before → EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial
        (lowerPlace owner (lowerEnv env.mod env.vars results) before).2)
    (exprChild : ∀ {type : Ty} {start finish : Nat},
      Core.tyExpr env expr start = .ok (type, finish) → ∀ {initial before : LS},
      GeneratedBuilderState before → EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial
        (lowerExpr expr (lowerEnv env.mod env.vars results) before).2)
    {initial before : LS} (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerExpr (.push owner expr origin) (lowerEnv env.mod env.vars results) before).2 := by
  obtain ⟨info, element, ownerStart, ownerFinish, childStart, childFinish,
    ownerSource, shape, childSource, _⟩ := tyExpr_push_children source
  let ownerValue := lowerPlace owner (lowerEnv env.mod env.vars results) before
  let value := lowerExpr expr (lowerEnv env.mod env.vars results) ownerValue.2
  have ownerBuilder := placeChild ownerSource generated builder
  have ownerGenerated := generated.lowerPlace owner (show lowerPlace owner _ before = ownerValue from rfl)
  have valueBuilder := exprChild childSource ownerGenerated ownerBuilder
  have rows : value.2.cur.isSome = true →
      ∃ mu, value.2.vals[ownerValue.1]? = some (some (.data (.ref mu info.ty))) ∧
        value.2.vals[value.1]? = some (some (.data element)) := by
    intro active
    have ownerLive := (dead_lowerExpr expr).live_before rfl active
    obtain ⟨mu, ownerTyped⟩ := outputs.place owner ownerSource generated rfl ownerLive
    exact ⟨mu, (types_lowerExpr expr _ ownerValue.2 _ _ rfl) _ _ ownerTyped,
      outputs.expression expr childSource ownerGenerated rfl active⟩
  apply valueBuilder.emitDef (.push ownerValue.1 value.1 origin)
  · intro active
    obtain ⟨mu, ownerTyped, valueTyped⟩ := rows active
    exact ⟨.data (.ref .mutable element), by
      dsimp only [value, ownerValue] at ownerTyped valueTyped ⊢
      simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, ownerTyped, shape, valueTyped,
        pure, Except.pure, bind, Except.bind]⟩
  · intro active operand member
    obtain ⟨mu, ownerTyped, valueTyped⟩ := rows active
    have either : operand = ownerValue.1 ∨ operand = value.1 := by simpa [Op.uses] using member
    rcases either with rfl | rfl
    · exact (Array.getElem?_eq_some_iff.mp ownerTyped).1
    · exact (Array.getElem?_eq_some_iff.mp valueTyped).1

end Goose.Lower.Validation

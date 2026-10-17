import Goose.Lower.GeneratedBuilder
import Goose.Lower.Validation.EmittedTypingPlaceCheckpoints

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure EmittedSourceResults (env : Core.TEnv) (results : List Ty) : Prop where
  expression : ∀ (expr : Expr) {type : Ty} {start finish : Nat},
    Core.tyExpr env expr start = .ok (type, finish) →
    ∀ {before after : LS} {value : ValueId}, GeneratedBuilderState before →
    lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, after) →
    after.cur.isSome = true → after.vals[value]? = some (some (.data type))
  place : ∀ (place : Place) {info : PlaceInfo} {start finish : Nat},
    Core.tyPlace env place start = .ok (info, finish) →
    ∀ {before after : LS} {value : ValueId}, GeneratedBuilderState before →
    lowerPlace place (lowerEnv env.mod env.vars results) before = (value, after) →
    after.cur.isSome = true → ∃ mu, after.vals[value]? = some (some (.data (.ref mu info.ty)))
  view : ∀ (view : View) {element : Ty} {writable : Bool} {start finish : Nat},
    Core.tyView env view start = .ok ((element, writable), finish) →
    ∀ {before after : LS} {value : ValueId}, GeneratedBuilderState before →
    lowerView view (lowerEnv env.mod env.vars results) before = (value, after) →
    after.cur.isSome = true → ∃ mu, after.vals[value]? = some (some (.view mu element))

theorem emitted_checked_read_source {env : Core.TEnv} {results : List Ty}
    (outputs : EmittedSourceResults env results) {place : Place} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env place start = .ok (info, finish))
    {initial before : LS} (generated : GeneratedBuilderState before)
    (child : EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerPlace place (lowerEnv env.mod env.vars results) before).2) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerExpr (.read place) (lowerEnv env.mod env.vars results) before).2 := by
  apply emitted_checked_lowerExpr_read place child
  intro block active
  obtain ⟨mu, row⟩ := outputs.place place source generated rfl (by simp [active])
  exact ⟨mu, info.ty, row⟩

end Goose.Lower.Validation

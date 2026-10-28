import Goose.Lower.ReflectionPlaces

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem PlaceSource.sliceReference_actual {cfg : Cfg} {env : Env} {state : St} {expression : Expr}
    (source : PlaceSource cfg env (.deref expression) state) {ty : Ty}
    (slice : sliceRefTy source.typingEnv expression = some ty) :
    ∃ (slot : VarId) (location : Loc), expression = .read (.var slot) ∧
      evalPlace 3 cfg env (.deref expression) state = .ok location state ∧
      PlaceOk cfg.mod source.world.G source.world.P source.rootsEnv env state.store (.deref expression) location source.ty := by
  obtain ⟨slot, descriptor, outer, mutability, element, expressionEq, visible, variableAt, variableType, flat, typeEq⟩ :=
    sliceRefTy_some slice
  subst expression
  have future : slot ∈ source.context.inputFuture := by
    cases context : source.context <;> simp [context, EvaluationContext.inputFuture,
      NodeContext.inputFuture, DemandNode.variables, Place.variables, Expr.variables]
  obtain ⟨actual, scope, value, found, scopeAt, _, stored, typed⟩ := source.frame.vis slot visible future
  rw [source.frame.vars_t, found] at variableAt
  cases variableAt
  rw [variableType] at typed
  obtain ⟨location, valueEq, referenceTyped⟩ := typed
  subst value
  have evaluated : evalPlace 3 cfg env (.deref (.read (.var slot))) state = .ok location state := by
    simp [evalPlace, evalExpr, rootOf, found, scopeAt, readLoc, read_root stored, bind_apply, pure_apply, expectRef]
  exact ⟨slot, location, rfl, evaluated, (source.result 3 location evaluated).typed⟩

#print axioms PlaceSource.sliceReference_actual
end Goose.Lower

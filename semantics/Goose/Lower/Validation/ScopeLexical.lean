import Goose.Lower.Validation.Scopes

namespace Goose.Lower.Validation

open Goose.Core

def ScopeTableContains (parents : Array (Option Nat)) (pairs : List (Nat × Option Nat)) : Prop :=
  ∀ scope parent, (scope, parent) ∈ pairs → parents[scope]? = some parent

theorem scopeParents_contains {pairs : List (Nat × Option Nat)}
    (checked : scopeOrderError pairs 0 = none) :
    ScopeTableContains (scopeParents pairs) pairs := by
  intro scope parent member
  obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
  have position := (scopeOrderError_lookup checked lookup).1
  simp only [Nat.zero_add] at position
  subst scope
  simp only [scopeParents, Array.getElem?_map, List.getElem?_toArray, lookup,
    Option.map_some]

theorem ScopeTableContains.append {parents : Array (Option Nat)}
    {left right : List (Nat × Option Nat)} :
    ScopeTableContains parents (left ++ right) ↔
      ScopeTableContains parents left ∧ ScopeTableContains parents right := by
  simp only [ScopeTableContains, List.mem_append]
  constructor
  · intro all
    exact ⟨fun scope parent member => all scope parent (Or.inl member),
      fun scope parent member => all scope parent (Or.inr member)⟩
  · rintro ⟨left, right⟩ scope parent (member | member)
    · exact left scope parent member
    · exact right scope parent member

theorem ScopeTableContains.block {parents : Array (Option Nat)} {parent : Option Nat}
    {scope : Nat} {stmts : List Stmt} {value : Option Expr}
    (contains : ScopeTableContains parents (blockScopes parent (.mk scope stmts value))) :
    parents[scope]? = some parent ∧
      ScopeTableContains parents (stmtsScopes (some scope) stmts) ∧
      ScopeTableContains parents (match value with
        | some expr => exprScopes (some scope) expr
        | none => []) := by
  cases value with
  | none =>
    change ScopeTableContains parents
      ((scope, parent) :: (stmtsScopes (some scope) stmts ++ [])) at contains
    refine ⟨contains scope parent (by simp), ?_, ?_⟩
    · intro child childParent member
      exact contains child childParent (by simp [member])
    · intro child childParent member
      cases member
  | some expr =>
    change ScopeTableContains parents
      ((scope, parent) :: (stmtsScopes (some scope) stmts ++ exprScopes (some scope) expr)) at contains
    refine ⟨contains scope parent (by simp), ?_, ?_⟩
    · intro child childParent member
      exact contains child childParent (by simp [member])
    · intro child childParent member
      exact contains child childParent (by simp [member])

theorem lowerImpl_lexicalScopeTable {module : Module} {impl : Impl}
    (checked : checkImpl module impl = .ok ()) :
    ScopeTableContains (lowerImpl module impl).scopes (blockScopes none impl.body) :=
  scopeParents_contains (checkImpl_scopeOrder checked)

theorem lowerGlobal_lexicalScopeTable {module : Module} {globalId : GlobalId} {global : Global}
    (checked : checkGlobal module globalId global = .ok ()) :
    ScopeTableContains (lowerGlobal module global).init.scopes (exprScopes none global.init) :=
  scopeParents_contains (checkGlobal_scopeOrder checked)

end Goose.Lower.Validation

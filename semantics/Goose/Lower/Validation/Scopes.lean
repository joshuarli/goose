import Goose.Lower.CoreToGir
import Goose.Core.Sound.Check

namespace Goose.Lower.Validation

open Goose.Core

theorem scopeOrderError_cons_success {scope start : Nat} {parent : Option Nat}
    {rest : List (Nat × Option Nat)}
    (checked : scopeOrderError ((scope, parent) :: rest) start = none) :
    scope = start ∧ (∀ value, parent = some value → value < scope) ∧
      scopeOrderError rest (start + 1) = none := by
  by_cases aligned : scope = start
  · subst scope
    cases parent with
    | none =>
      refine ⟨rfl, by simp, ?_⟩
      simpa [scopeOrderError] using checked
    | some value =>
      by_cases earlier : value < start
      · refine ⟨rfl, ?_, ?_⟩
        · intro other equality
          cases equality
          exact earlier
        · simpa [scopeOrderError, earlier] using checked
      · simp [scopeOrderError, earlier] at checked
  · simp [scopeOrderError, aligned] at checked

theorem scopeOrderError_lookup {pairs : List (Nat × Option Nat)} {start index scope : Nat}
    {parent : Option Nat} (checked : scopeOrderError pairs start = none)
    (lookup : pairs[index]? = some (scope, parent)) :
    scope = start + index ∧ ∀ value, parent = some value → value < scope := by
  induction pairs generalizing start index with
  | nil => simp at lookup
  | cons first rest inductionHypothesis =>
    obtain ⟨scopeMatches, parentEarlier, restChecked⟩ := scopeOrderError_cons_success checked
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
      cases lookup
      exact ⟨by simpa using scopeMatches, parentEarlier⟩
    | succ index =>
      have tailLookup : rest[index]? = some (scope, parent) := by simpa using lookup
      obtain ⟨indexMatches, earlier⟩ := inductionHypothesis restChecked tailLookup
      exact ⟨by omega, earlier⟩

theorem scopeParents_earlier {pairs : List (Nat × Option Nat)}
    (checked : scopeOrderError pairs 0 = none) (index parent : Nat)
    (lookup : (scopeParents pairs)[index]? = some (some parent)) : parent < index := by
  simp only [scopeParents, Array.getElem?_map, List.getElem?_toArray] at lookup
  cases pair : pairs[index]? with
  | none => simp [pair] at lookup
  | some value =>
    obtain ⟨scope, sourceParent⟩ := value
    simp only [pair, Option.map_some, Option.some.injEq] at lookup
    have facts := scopeOrderError_lookup checked pair
    exact by simpa [facts.1] using facts.2 parent lookup

theorem checkImpl_scopeOrder {module : Module} {impl : Impl}
    (checked : checkImpl module impl = .ok ()) :
    scopeOrderError (blockScopes none impl.body) 0 = none := by
  cases order : scopeOrderError (blockScopes none impl.body) 0 with
  | none => rfl
  | some message =>
    simp only [checkImpl, order] at checked
    simp [chk] at checked

theorem checkGlobal_scopeOrder {module : Module} {index : GlobalId} {global : Global}
    (checked : checkGlobal module index global = .ok ()) :
    scopeOrderError (exprScopes none global.init) 0 = none := by
  cases order : scopeOrderError (exprScopes none global.init) 0 with
  | none => rfl
  | some message =>
    simp only [checkGlobal, order] at checked
    simp [chk] at checked

theorem lowerImplAt_scopeParents_earlier {module : Module} {implId : ImplId} {impl : Impl}
    (checked : checkImpl module impl = .ok ()) (index parent : Nat)
    (lookup : (lowerImplAt module implId impl).scopes[index]? = some (some parent)) :
    parent < index :=
  scopeParents_earlier (checkImpl_scopeOrder checked) index parent lookup

theorem lowerGlobal_scopeParents_earlier {module : Module} {globalId : GlobalId} {global : Global}
    (checked : checkGlobal module globalId global = .ok ()) (index parent : Nat)
    (lookup : (lowerGlobal module global).init.scopes[index]? = some (some parent)) :
    parent < index :=
  scopeParents_earlier (checkGlobal_scopeOrder checked) index parent lookup

end Goose.Lower.Validation

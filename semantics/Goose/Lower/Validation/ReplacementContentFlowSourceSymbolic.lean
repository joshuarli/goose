import Goose.Lower.Validation.ReplacementContentFlowSourceRoots
import Goose.GIR.ReplacementContentFlowProofsNormalization

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

def symbolicRoots (func : Func) (roots : Roots) : Option (List RootRef) :=
  normalize { func with roots := { func.roots with params := #[] } } roots

private theorem unspecialized_expand (func : Func) (root : RootRef) :
    ({ func with roots := { func.roots with params := #[] } } : Func).expandParameterRoot root = [root] := by
  cases root <;> simp [Func.expandParameterRoot, Func.parameterRoots]

private theorem unspecialized_flatMap (func : Func) (roots : List RootRef) :
    roots.flatMap ({ func with roots := { func.roots with params := #[] } } : Func).expandParameterRoot = roots := by
  have identity : ({ func with roots := { func.roots with params := #[] } } : Func).expandParameterRoot =
      fun root => [root] := funext (unspecialized_expand func)
  rw [identity]
  simp

private theorem normalizeAtom_symbolic (func : Func) (atom : Atom) :
    normalizeAtom func atom =
      (normalizeAtom { func with roots := { func.roots with params := #[] } } atom).map
        (·.flatMap func.expandParameterRoot) := by
  cases atom with
  | «local» slot => simp [normalizeAtom, Func.expandParameterRoot]
  | global global => simp [normalizeAtom, Func.expandParameterRoot]
  | param index => simp [normalizeAtom, Func.expandParameterRoot, Func.parameterRoots]
  | contents index =>
    cases found : func.roots.contents.find? (·.1 == index) with
    | none => simp [normalizeAtom, found]
    | some row =>
      simp only [normalizeAtom, found, Option.map_some]
      change some (row.2.flatMap func.expandParameterRoot) =
        some ((row.2.flatMap ({ func with roots := { func.roots with params := #[] } } : Func).expandParameterRoot).flatMap func.expandParameterRoot)
      rw [unspecialized_flatMap]

theorem symbolicRoots_parameter (func : Func) (index : Nat) :
    symbolicRoots func (.known [.param index]) = some [.param index] := by
  simp [symbolicRoots, normalize, normalizeAtom, Func.parameterRoots, unionRoots]

theorem symbolicRoots_actual_within {func : Func} {roots : Roots} {symbolic : List RootRef}
    (known : symbolicRoots func roots = some symbolic) :
    ∃ actual, normalize func roots = some actual ∧
      ∀ root ∈ actual, root ∈ symbolic.flatMap func.expandParameterRoot := by
  cases roots with
  | pending => simp [symbolicRoots, normalize] at known
  | unknown => simp [symbolicRoots, normalize] at known
  | known atoms =>
    have atomBounds := (normalize_fold_atoms _ atoms [] symbolic known).2
    obtain ⟨actual, normalized, within⟩ := normalize_fold_within func atoms
      (symbolic.flatMap func.expandParameterRoot) (by
        intro atom member
        obtain ⟨raw, rawKnown, rawWithin⟩ := atomBounds atom member
        refine ⟨raw.flatMap func.expandParameterRoot, ?_, ?_⟩
        · rw [normalizeAtom_symbolic, rawKnown]
          rfl
        · intro root included
          obtain ⟨sourceRoot, sourceMember, expanded⟩ := List.mem_flatMap.mp included
          exact List.mem_flatMap.mpr ⟨sourceRoot, rawWithin sourceMember, expanded⟩) [] (by simp)
    exact ⟨actual, normalized, within⟩

#print axioms symbolicRoots_parameter
#print axioms symbolicRoots_actual_within

theorem symbolicRoots_contents {func : Func} {index : Nat} {roots : List RootRef}
    (annotation : func.roots.contents.find? (·.1 == index) = some (index, roots)) :
    symbolicRoots func (.known [.contents index]) = some (unionRoots [] roots) := by
  unfold symbolicRoots
  rw [normalize_contents (func := { func with roots := { func.roots with params := #[] } }) annotation]
  rw [unspecialized_flatMap]

def SymbolicRootsWithin (func : Func) (roots : Roots) (upper : List RootRef) : Prop :=
  roots = .pending ∨ ∃ actual, symbolicRoots func roots = some actual ∧ actual ⊆ upper

theorem SymbolicRootsWithin.join {func : Func} {left right : Roots} {upper : List RootRef}
    (leftBound : SymbolicRootsWithin func left upper)
    (rightBound : SymbolicRootsWithin func right upper) :
    SymbolicRootsWithin func (left.join right) upper := by
  rcases leftBound with pending | ⟨leftRoots, leftKnown, leftWithin⟩
  · subst left
    have identity : Roots.pending.join right = right := by cases right <;> rfl
    rwa [identity]
  · rcases rightBound with pending | ⟨rightRoots, rightKnown, rightWithin⟩
    · subst right
      have identity : left.join Roots.pending = left := by cases left <;> rfl
      rw [identity]
      exact Or.inr ⟨leftRoots, leftKnown, leftWithin⟩
    · obtain ⟨actual, known, within⟩ := normalize_join_known
        { func with roots := { func.roots with params := #[] } }
        left right leftRoots rightRoots leftKnown rightKnown
      exact Or.inr ⟨actual, known, fun root member => (within root member).elim (fun included => leftWithin included) (fun included => rightWithin included)⟩

theorem SymbolicRootsWithin.actual_within {func : Func} {roots : Roots} {upper : List RootRef}
    (bound : SymbolicRootsWithin func roots upper) (ready : roots ≠ .pending) :
    ∃ actual, normalize func roots = some actual ∧
      ∀ root ∈ actual, root ∈ upper.flatMap func.expandParameterRoot := by
  rcases bound with pending | ⟨symbolic, known, within⟩
  · exact False.elim (ready pending)
  · obtain ⟨actual, normalized, expanded⟩ := symbolicRoots_actual_within known
    refine ⟨actual, normalized, ?_⟩
    intro root member
    obtain ⟨sourceRoot, sourceMember, concrete⟩ := List.mem_flatMap.mp (expanded root member)
    exact List.mem_flatMap.mpr ⟨sourceRoot, within sourceMember, concrete⟩

#print axioms symbolicRoots_contents
#print axioms SymbolicRootsWithin.join
#print axioms SymbolicRootsWithin.actual_within

end Goose.Lower.Validation.ReplacementContentFlowSource

import Goose.GIR.ReplacementContentFlowProofsAssignedOriginsSubstitution
import Goose.GIR.ReplacementContentFlowProofsTransfer

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem normalize_nonpending {func : Func} {roots : Roots} {actual : List RootRef}
    (normalized : normalize func roots = some actual) : roots ≠ .pending := by
  intro same
  simp [same, normalize] at normalized

theorem normalize_not_unknown {func : Func} {roots : Roots} {actual : List RootRef}
    (normalized : normalize func roots = some actual) : roots ≠ .unknown := by
  intro same
  simp [same, normalize] at normalized

theorem substitute_nonpending_of_normalized (func callee : Func) (state : State)
    (arguments : List ValueId) (roots : Roots) (actual : List RootRef)
    (normalized : normalize callee roots = some actual)
    (operands : ∀ value ∈ arguments, flowAt state.values value ≠ .pending)
    (contents : ∀ index,
      (callee.roots.contents.find? (·.1 == index)).isSome = true →
      ∀ value, arguments[index]? = some value →
        content func state (flowAt state.values value) ≠ .pending) :
    substitute func state arguments roots ≠ .pending := by
  apply substitute_nonpending func state arguments roots (normalize_nonpending normalized)
  · intro atoms same index member value found
    exact operands value (List.mem_of_getElem? found)
  · intro atoms same index member value found
    subst roots
    obtain ⟨mapped, present, _⟩ := (normalize_fold_atoms callee atoms [] actual normalized).2
      (.contents index) member
    have declared : (callee.roots.contents.find? (·.1 == index)).isSome = true := by
      cases row : callee.roots.contents.find? (·.1 == index) with
      | none => simp [normalizeAtom, row] at present
      | some entry => simp
    exact contents index declared value found

#print axioms substitute_nonpending_of_normalized

end Goose.GIR.ReplacementContentFlow.Model

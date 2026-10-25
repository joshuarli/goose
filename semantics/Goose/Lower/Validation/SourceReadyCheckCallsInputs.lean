import Goose.Lower.Validation.SourceReadyCheckCallsScalar
import Goose.Lower.Validation.ReplacementContentFlowSourceParameterAdmissions
import Goose.Lower.Validation.ReplacementContentFlowSourceInputFold

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem admitted_scalar_argument_empty {callee : Func} {argumentRoots : Nat → Option (List RootRef)}
    {index : Nat} {type : Ty} {actual : List RootRef}
    (parameter : callee.params[index]? = some type) (scalar : type.isRefLike = false)
    (known : argumentRoots index = some actual) :
    ∃ bound, admittedArgumentBound callee argumentRoots index = some bound ∧ bound.covers (some []) = true := by
  cases row : callee.roots.params.find? (·.1 == index) with
  | none => exact ⟨.roots actual, by simp [admittedArgumentBound, parameter, known, row], rfl⟩
  | some entry =>
    obtain ⟨key, declared⟩ := entry
    refine ⟨.roots (unionRoots actual (declared.filterMap fun
      | .global global => some (.global global)
      | _ => none)), ?_, rfl⟩
    simp [admittedArgumentBound, parameter, known, row, scalar]
    rfl

private theorem content_row_lookup_list (rows : List (Nat × List RootRef))
    (unique : (rows.map Prod.fst).Nodup) {index : Nat} {roots : List RootRef}
    (member : (index, roots) ∈ rows) : rows.find? (·.1 == index) = some (index, roots) := by
  induction rows with
  | nil => cases member
  | cons head rest ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | member
    · subst head
      simp
    · have different : head.1 ≠ index := by
        intro same
        exact unique.1 (List.mem_map.mpr ⟨(index, roots), member, same.symm⟩)
      simpa [different] using ih unique.2 member

theorem content_row_lookup {callee : Func} {index : Nat} {roots : List RootRef}
    (unique : (callee.roots.contents.toList.map Prod.fst).Nodup)
    (member : (index, roots) ∈ callee.roots.contents.toList) :
    callee.roots.contents.find? (·.1 == index) = some (index, roots) := by
  rw [← Array.find?_toList]
  exact content_row_lookup_list _ unique member

end Goose.Lower.Validation.ReplacementContentFlowSource

import Goose.Lower.Validation.ReplacementContentFlowSourceReadyCallees
import Goose.GIR.ReplacementContentFlowProofsCanonicalClosure

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem checkWrites_of_canonical {func : Func} {types : Array (Option VTy)}
    {provenance : Prov} {state : State}
    (canonical : state.CanonicalWithin func types provenance)
    (parameters : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (unique : (func.roots.contents.toList.map Prod.fst).Nodup)
    (ready : ∀ (index : Nat) (roots : Roots), state.writes[index]? = some (.assigned roots) → roots ≠ .pending) :
    checkWrites func state = true := by
  unfold checkWrites
  apply List.all_eq_true.mpr
  intro pair member
  rcases pair with ⟨write, index⟩
  have cellRow : state.writes[index]? = some write := by
    simpa only [Array.getElem?_toList] using List.mk_mem_zipIdx_iff_getElem?.mp member
  have bounded := (Array.getElem?_eq_some_iff.mp cellRow).1
  cases write with
  | unchanged => rfl
  | assigned roots =>
    have assigned : state.writes[index]?.getD (.assigned .unknown) = .assigned roots := by simp [cellRow]
    have observed := canonical.writeRows index bounded roots assigned
    have raw := canonical.memory.writes index bounded
    rw [assigned] at raw
    change SymbolicRootsRefine func roots (func.contentRoots index) at raw
    obtain ⟨actual, known, within⟩ := raw.actual parameters (ready index roots cellRow)
    cases row : func.roots.contents.find? (·.1 == index) with
    | none => simp [row] at observed
    | some declared =>
      rw [contentRoots_find unique index, row] at within
      simp only [Option.map_some, Option.getD_some] at within
      simp only [Bool.or_eq_true]
      apply Or.inr
      simp only [row, Option.any_some, rootsWithin, known, Option.any_some]
      exact List.all_eq_true.mpr (fun root member => List.contains_iff_mem.mpr (within member))

#print axioms checkWrites_of_canonical

end Goose.Lower.Validation.ReplacementContentFlowSource

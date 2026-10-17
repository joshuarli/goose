import Goose.Lower.Validation.SummaryPreservationResults

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem resultRoots_go_retains
    {one : Array (List RootRef) → Array (List RootRef) × Bool}
    {seeds initial : Array (List RootRef)}
    (rounds : ∀ current, RootsBelow seeds current → RootsBelow seeds (one current).1)
    (start : RootsBelow seeds initial) (fuel : Nat) :
    RootsBelow seeds (resultRoots.go one fuel initial) := by
  induction fuel generalizing initial with
  | zero => exact start
  | succ fuel ih =>
    rw [resultRoots.go]
    cases step : one initial with
    | mk next changed =>
      have nextBounded := rounds initial start
      rw [step] at nextBounded
      dsimp only at nextBounded ⊢
      split
      · exact ih nextBounded
      · exact nextBounded

theorem resultRoots_retains_declared {module : GIR.Module} {types : Array (Array (Option VTy))}
    (covered : module.funcs.size ≤ types.size) :
    RootsBelow module.declaredResultRoots (resultRoots module types) := by
  unfold resultRoots
  apply resultRoots_go_retains
  · intro current retained index root member
    have functionBound : index < module.funcs.size := by
      by_cases inside : index < module.funcs.size
      · exact inside
      apply False.elim
      have absent : module.funcs[index]? = none := Array.getElem?_eq_none (by omega)
      simp [rootsAt, Module.declaredResultRoots, Array.getElem?_map, absent] at member
    have typeBound : index < types.size := Nat.lt_of_lt_of_le functionBound covered
    have functionRow := Array.getElem?_eq_getElem functionBound
    have typeRow := Array.getElem?_eq_getElem typeBound
    have paired : (module.funcs.zip types)[index]? = some (module.funcs[index], types[index]) :=
      Array.getElem?_zip_eq_some.mpr ⟨functionRow, typeRow⟩
    simp only [rootsAt, Array.getElem?_mapIdx, paired, Option.map_some, Option.getD_some]
    exact unionRoots_left _ _ root (retained index root member)
  · exact fun _ _ member => member

#print axioms resultRoots_retains_declared

end Goose.Lower.Validation.SummaryPreservation

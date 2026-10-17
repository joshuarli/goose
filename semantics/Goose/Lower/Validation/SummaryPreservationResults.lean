import Goose.Lower.Validation.SummaryPreservationProvenance

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem resultRoots_go_below
    {one : Array (List RootRef) → Array (List RootRef) × Bool}
    {upper initial : Array (List RootRef)}
    (rounds : ∀ current, RootsBelow current upper → RootsBelow (one current).1 upper)
    (start : RootsBelow initial upper) (fuel : Nat) :
    RootsBelow (resultRoots.go one fuel initial) upper := by
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

theorem resultRoots_below {module : Goose.GIR.Module} {vts : Array (Array (Option VTy))}
    {upper : Array (List RootRef)}
    (returned : ∀ candidate, RootsBelow candidate upper →
      ∀ index func types, (module.funcs.zip vts)[index]? = some (func, types) →
        ∀ root ∈ func.returnedRoots (func.provenance candidate types
          (module.globals.size + module.funcs.foldl
            (fun n func => n + func.params.length + func.slots.size) 0)),
          root ∈ rootsAt upper index) :
    RootsBelow (resultRoots module vts) upper := by
  unfold resultRoots
  apply resultRoots_go_below
  · intro candidate bounded index root member
    dsimp only at member
    simp only [rootsAt, Array.getElem?_mapIdx] at member
    cases lookup : (module.funcs.zip vts)[index]? with
    | none => simp [lookup] at member
    | some pair =>
      rcases pair with ⟨func, types⟩
      simp only [lookup, Option.map_some, Option.getD_some] at member
      rcases mem_unionRoots_iff.mp member with prior | body
      · exact bounded _ _ prior
      · exact returned candidate bounded index func types lookup root body
  · intro index root member
    simp only [rootsAt, Array.getElem?_map] at member
    cases lookup : module.funcs[index]? <;> simp [lookup] at member

end Goose.Lower.Validation.SummaryPreservation

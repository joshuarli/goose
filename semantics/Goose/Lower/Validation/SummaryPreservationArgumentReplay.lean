import Goose.Lower.Validation.SummaryPreservationRootRefinement
import Goose.Lower.Validation.DeadFrontier

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def ArgumentReplay (env : PEnv) : Arg → RState → List RootRef → RState → Prop
  | .byVal expression, before, roots, after => rpExpr env expression before = .ok (roots, after)
  | .byRef _ place, before, roots, after => rpPlace env place before = .ok (roots, after)


theorem rpArgs_cons_contract {env : PEnv} {argument : Arg} {rest : List Arg}
    {before after : RState} {roots : List (List RootRef)}
    (source : rpArgs env (argument :: rest) before = .ok (roots, after)) :
    ∃ first middle remaining,
      ArgumentReplay env argument before first middle ∧
      rpArgs env rest middle = .ok (remaining, after) ∧ roots = first :: remaining := by
  cases argument <;> simp only [rpArgs] at source
  all_goals
    obtain ⟨first, middle, firstRun, tail⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨remaining, final, restRun, finish⟩ := (st_bind_ok _ _ _ _).mp tail
    have pair := (st_pure_ok _ _ _).mp finish
    have sameRoots : roots = first :: remaining := congrArg Prod.fst pair
    have sameState : after = final := congrArg Prod.snd pair
    subst final
    exact ⟨first, middle, remaining, firstRun, restRun, sameRoots⟩


theorem lowerArgs_source_root_composition {env : PEnv} {le : LEnv} {func : Func}
    (Ready : List Arg → RState → LS → Prov → Prop)
    (sizes : ∀ remaining source ls upper, Ready remaining source ls upper → upper.vals.size = ls.vals.size)
    (step : ∀ argument rest before after roots ls upper,
      Ready (argument :: rest) before ls upper → ArgumentReplay env argument before roots after →
      ∃ next,
        Ready rest after (lowerArg argument le ls).2 next ∧
        next.slots = upper.slots ∧
        (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
        ((lowerArg argument le ls).2.cur.isSome = true →
          (lowerArg argument le ls).1 < (lowerArg argument le ls).2.vals.size ∧
          RootsRefine func (rootsAt next.vals (lowerArg argument le ls).1) roots))
    (arguments : List Arg) {before after : RState} {sourceRoots : List (List RootRef)}
    {ls : LS} {upper : Prov} (ready : Ready arguments before ls upper)
    (source : rpArgs env arguments before = .ok (sourceRoots, after)) :
    ∃ next,
      Ready [] after (lowerArgs arguments le ls).2 next ∧ next.slots = upper.slots ∧
      (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
      ((lowerArgs arguments le ls).2.cur.isSome = true →
        (lowerArgs arguments le ls).1.length = sourceRoots.length ∧
        ∀ (index : Nat) (value : ValueId), (lowerArgs arguments le ls).1[index]? = some value →
          ∃ roots, sourceRoots[index]? = some roots ∧
            RootsRefine func (rootsAt next.vals value) roots ∧
            value < (lowerArgs arguments le ls).2.vals.size) := by
  induction arguments generalizing before after sourceRoots ls upper with
  | nil =>
    have pair := (st_pure_ok _ _ _).mp source
    have sameRoots : sourceRoots = [] := congrArg Prod.fst pair
    have sameState : after = before := congrArg Prod.snd pair
    subst sourceRoots
    subst after
    refine ⟨upper, ready, rfl, fun _ _ => rfl, ?_⟩
    intro live
    refine ⟨rfl, ?_⟩
    intro index value lookup
    simp [lowerArgs, pure_run] at lookup
  | cons argument rest ih =>
    obtain ⟨firstRoots, middleSource, remainingRoots, firstSource, remainingSource, rootList⟩ :=
      rpArgs_cons_contract source
    subst sourceRoots
    obtain ⟨middle, middleReady, middleSlots, middlePrefix, middleValue⟩ :=
      step argument rest before middleSource firstRoots ls upper ready firstSource
    obtain ⟨next, nextReady, nextSlots, nextPrefix, nextValues⟩ := ih middleReady remainingSource
    let first := lowerArg argument le ls
    let tail := lowerArgs rest le first.2
    have whole : lowerArgs (argument :: rest) le ls = (first.1 :: tail.1, tail.2) := by
      simp only [lowerArgs, bind_run, pure_run]
      rfl
    rw [whole]
    have sizeGrowth : upper.vals.size ≤ middle.vals.size := by
      rw [sizes _ _ _ _ ready, sizes _ _ _ _ middleReady]
      exact (advB_lowerArg argument le ls first.1 first.2 rfl).vals
    refine ⟨next, nextReady, nextSlots.trans middleSlots, ?_, ?_⟩
    · intro index bound
      exact (nextPrefix index (Nat.lt_of_lt_of_le bound sizeGrowth)).trans (middlePrefix index bound)
    · intro live
      have middleLive : first.2.cur.isSome = true :=
        (dead_lowerArgs rest).live_before (le := le) (before := first.2)
          (after := tail.2) (result := tail.1) rfl live
      obtain ⟨firstBound, firstRefined⟩ := middleValue middleLive
      obtain ⟨remainingLength, remainingValues⟩ := nextValues live
      refine ⟨by simpa using congrArg Nat.succ remainingLength, ?_⟩
      intro index value lookup
      cases index with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
        subst value
        refine ⟨firstRoots, by simp, ?_, ?_⟩
        · rw [nextPrefix first.1 (by rw [sizes _ _ _ _ middleReady]; exact firstBound)]
          exact firstRefined
        · exact Nat.lt_of_lt_of_le firstBound
            (advB_lowerArgs rest le first.2 tail.1 tail.2 rfl).vals
      | succ index =>
        simp only [List.getElem?_cons_succ] at lookup
        obtain ⟨roots, sourceLookup, refined, bound⟩ := remainingValues index value lookup
        exact ⟨roots, by simpa only [List.getElem?_cons_succ] using sourceLookup, refined, bound⟩

end Goose.Lower.Validation.SummaryPreservation

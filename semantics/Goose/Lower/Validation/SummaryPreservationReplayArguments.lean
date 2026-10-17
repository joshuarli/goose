import Goose.Lower.Validation.SummaryPreservationReplayReferences
import Goose.Lower.Validation.DeadFrontier

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def ArgumentReplay (env : PEnv) (argument : Arg) (before : RState)
    (roots : List RootRef) (after : RState) : Prop :=
  match argument with
  | .byVal expression => rpExpr env expression before = .ok (roots, after)
  | .byRef _ place => rpPlace env place before = .ok (roots, after)

theorem rpArgs_cons_contract {env : PEnv} {argument : Arg} {rest : List Arg}
    {before after : RState} {sourceRoots : List (List RootRef)}
    (source : rpArgs env (argument :: rest) before = .ok (sourceRoots, after)) :
    ∃ roots remaining middle, ArgumentReplay env argument before roots middle ∧
      rpArgs env rest middle = .ok (remaining, after) ∧ sourceRoots = roots :: remaining := by
  cases argument with
  | byVal expression =>
    obtain ⟨roots, middle, first, tail⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨remaining, finish, restReplay, result⟩ := (st_bind_ok _ _ _ _).mp tail
    have equal := (st_pure_ok _ _ _).mp result
    cases equal
    exact ⟨roots, remaining, middle, first, restReplay, rfl⟩
  | byRef mutability place =>
    obtain ⟨roots, middle, first, tail⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨remaining, finish, restReplay, result⟩ := (st_bind_ok _ _ _ _).mp tail
    have equal := (st_pure_ok _ _ _).mp result
    cases equal
    exact ⟨roots, remaining, middle, first, restReplay, rfl⟩

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem argument {env : PEnv} (argument : Arg) {before after : RState} {sourceRoots : List RootRef}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : ArgumentReplay env argument before sourceRoots after)
    (expressionChild : ∀ expression, argument = .byVal expression →
      rpExpr env expression before = .ok (sourceRoots, after) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerExpr expression le ls).2 next ∧
        ((lowerExpr expression le ls).2.cur.isSome = true →
          (lowerExpr expression le ls).1 < (lowerExpr expression le ls).2.vals.size ∧
          RootsRefine func (rootsAt next.vals (lowerExpr expression le ls).1) sourceRoots) ∧
        ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index)
    (placeChild : ∀ mutability place, argument = .byRef mutability place →
      rpPlace env place before = .ok (sourceRoots, after) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerPlace place le ls).2 next ∧
        ((lowerPlace place le ls).2.cur.isSome = true →
          (lowerPlace place le ls).1 < (lowerPlace place le ls).2.vals.size ∧
          RootsRefine func (rootsAt next.vals (lowerPlace place le ls).1) sourceRoots) ∧
        ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerArg argument le ls).2 next ∧
      ((lowerArg argument le ls).2.cur.isSome = true →
        (lowerArg argument le ls).1 < (lowerArg argument le ls).2.vals.size ∧
        RootsRefine func (rootsAt next.vals (lowerArg argument le ls).1) sourceRoots) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases argument with
  | byVal expression => exact expressionChild expression rfl source
  | byRef mutability place =>
    obtain ⟨middle, generated, address, retained⟩ := placeChild mutability place rfl source
    obtain ⟨next, borrowed, returned, nextRoots⟩ := generated.borrowReference mutability Ty.unit
      (lowerPlace place le ls).1 sourceRoots address
    have whole : lowerArg (.byRef mutability place) le ls =
        borrowTo mutability (lowerPlace place le ls).1 le (lowerPlace place le ls).2 := by
      simp only [lowerArg, bind_run]
    rw [whole]
    refine ⟨next, borrowed, fun live => ⟨(returned live).bound, (returned live).refined⟩, ?_⟩
    intro index bound
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, generated.roots.valueSize]
      exact (advB_lowerPlace place le ls _ _ rfl).vals
    exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (retained index bound)

theorem arguments {env : PEnv} (syntaxArgs : List Arg)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (step : ∀ argument, argument ∈ syntaxArgs → ∀ before after roots state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ArgumentReplay env argument before roots after →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerArg argument le state).2 next ∧
        ((lowerArg argument le state).2.cur.isSome = true →
          (lowerArg argument le state).1 < (lowerArg argument le state).2.vals.size ∧
          RootsRefine func (rootsAt next.vals (lowerArg argument le state).1) roots) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    {before after : RState} {sourceRoots : List (List RootRef)}
    (source : rpArgs env syntaxArgs before = .ok (sourceRoots, after)) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerArgs syntaxArgs le ls).2 next ∧
      ((lowerArgs syntaxArgs le ls).2.cur.isSome = true →
        (lowerArgs syntaxArgs le ls).1.length = sourceRoots.length ∧
        ∀ (index : Nat) (value : ValueId), (lowerArgs syntaxArgs le ls).1[index]? = some value →
          value < (lowerArgs syntaxArgs le ls).2.vals.size ∧
          ∃ roots, sourceRoots[index]? = some roots ∧ RootsRefine func (rootsAt next.vals value) roots) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  induction syntaxArgs generalizing before after sourceRoots ls upper with
  | nil =>
    have equal := (st_pure_ok _ _ _).mp source
    cases equal
    refine ⟨upper, ready, ?_, fun _ _ => rfl⟩
    simp [lowerArgs, pure_run]
  | cons argument rest ih =>
    obtain ⟨roots, remaining, middleSource, firstReplay, restReplay, rfl⟩ := rpArgs_cons_contract source
    obtain ⟨middle, middleReady, firstValue, middleRoots⟩ :=
      step argument (by simp) before middleSource roots ls upper ready firstReplay
    obtain ⟨next, nextReady, tailValues, nextRoots⟩ := ih middleReady
      (fun child member => step child (by simp [member])) restReplay
    let first := lowerArg argument le ls
    let tail := lowerArgs rest le first.2
    have whole : lowerArgs (argument :: rest) le ls = (first.1 :: tail.1, tail.2) := by
      simp only [lowerArgs, bind_run, pure_run]
      rfl
    have valGrowth := (advB_lowerArgs rest le first.2 tail.1 tail.2 rfl).vals
    rw [whole]
    refine ⟨next, nextReady, ?_, ?_⟩
    · intro live
      have firstLive : first.2.cur.isSome = true :=
        (dead_lowerArgs rest).live_before (le := le) (before := first.2)
          (after := tail.2) (result := tail.1) rfl live
      obtain ⟨tailLength, tailValue⟩ := tailValues live
      refine ⟨by simpa using congrArg Nat.succ tailLength, ?_⟩
      intro index value row
      cases index with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at row
        subst value
        obtain ⟨bound, refined⟩ := firstValue firstLive
        refine ⟨Nat.lt_of_lt_of_le bound valGrowth, roots, rfl, ?_⟩
        rw [nextRoots first.1 (by rw [middleReady.roots.valueSize]; exact bound)]
        exact refined
      | succ index =>
        simp only [List.getElem?_cons_succ] at row
        obtain ⟨bound, sourceRoots, sourceRow, refined⟩ := tailValue index value row
        exact ⟨bound, sourceRoots, sourceRow, refined⟩
    · intro index bound
      have growth : upper.vals.size ≤ middle.vals.size := by
        rw [ready.roots.valueSize, middleReady.roots.valueSize]
        exact (advB_lowerArg argument le ls first.1 first.2 rfl).vals
      exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots index bound)

end ReplayBuilder

end Goose.Lower.Validation.SummaryPreservation

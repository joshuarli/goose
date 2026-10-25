import Goose.Lower.Validation.SummaryPreservationReplayLiveEmit
import Goose.Lower.Validation.SummaryPreservationRefinedEffects

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem slice {env : PEnv} {view : View} {low high : Bound} {origin : OriginId}
    {initialSource viewState lowState before after : RState} {viewRoots sourceRoots : List RootRef}
    {initial viewLS lowLS : LS} {viewValue : ValueId} {lowValue highValue : Bnd}
    (mutability : Mutability) (element : Ty)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (viewReplay : rpView env view initialSource = .ok (viewRoots, viewState))
    (lowReplay : rpBound env low viewState = .ok ((), lowState))
    (highReplay : rpBound env high lowState = .ok ((), before))
    (source : rpExpr env (.slice mutability view low high origin) initialSource = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (viewRun : lowerView view le initial = (viewValue, viewLS))
    (lowRun : lowerBound low le viewLS = (lowValue, lowLS))
    (highRun : lowerBound high le lowLS = (highValue, ls))
    (originBound : origin < le.mod.origins.size)
    (input : ls.cur.isSome = true → viewValue < ls.vals.size ∧
      (∀ value ∈ lowValue.uses, value < ls.vals.size) ∧
      (∀ value ∈ highValue.uses, value < ls.vals.size) ∧
      RootsRefine func (rootsAt upper.vals viewValue) viewRoots) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.slice mutability view low high origin) le initial).2 next ∧
      ((lowerExpr (.slice mutability view low high origin) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.slice mutability view low high origin) le initial).2
          (lowerExpr (.slice mutability view low high origin) le initial).1 sourceRoots (.data (.slice mutability element))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have replay : rpExpr env (.slice mutability view low high origin) initialSource =
      .ok (viewRoots, { before with eff := { before.eff with aborts := true } }) := by
    simp [rpExpr, viewReplay, lowReplay, highReplay, noteAborts, bind, pure, modify,
      Except.bind, Except.pure, StateT.bind, StateT.pure, StateT.modifyGet, modifyGet, MonadStateOf.modifyGet]
  rw [replay] at source
  cases source
  have whole : lowerExpr (.slice mutability view low high origin) le initial =
      Goose.Lower.emitDef (.viewSlice mutability viewValue lowValue highValue (some origin)) le ls := by
    simp only [lowerExpr, bind_run, viewRun, lowRun, highRun]
  rw [whole]
  apply ready.emitTypedDef_live (.viewSlice mutability viewValue lowValue highValue (some origin)) viewRoots
    (.data (.slice mutability element))
  · intro live value member
    simp only [Op.uses, List.mem_cons, List.mem_append] at member
    rcases member with same | lowMember | highMember
    · subst value
      exact (input live).1
    · exact (input live).2.1 value lowMember
    · exact (input live).2.2.1 value highMember
  · simpa [Op.origin] using originBound
  · simp [Op.SymbolRefsValid]
  · intro _
    have aborts := (effectRefinement_noteAborts (effectRefinement_empty func before.eff)).trans wholeEffect
    cases lowValue <;> cases highValue <;> first
      | exact effectRefinement_empty func target
      | exact aborts
  · intro live
    exact (input live).2.2.2
  · simp [VTy.refLike, Ty.isRefLike]

theorem length {env : PEnv} {view : View} {before afterView after : RState}
    {viewRoots sourceRoots : List RootRef} {initial : LS} {viewValue : ValueId}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (viewReplay : rpView env view before = .ok (viewRoots, afterView))
    (source : rpExpr env (.len view) before = .ok (sourceRoots, after))
    (viewRun : lowerView view le initial = (viewValue, ls))
    (input : ls.cur.isSome = true → viewValue < ls.vals.size) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.len view) le initial).2 next ∧
      ((lowerExpr (.len view) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.len view) le initial).2
          (lowerExpr (.len view) le initial).1 sourceRoots (.data (.int .i64))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have replay : rpExpr env (.len view) before = .ok ([], afterView) := by
    simp [rpExpr, viewReplay, bind, pure, Except.bind, Except.pure, StateT.bind, StateT.pure]
  rw [replay] at source
  cases source
  have whole : lowerExpr (.len view) le initial = Goose.Lower.emitDef (.viewLen viewValue) le ls := by
    simp only [lowerExpr, bind_run, viewRun]
  rw [whole]
  apply ready.emitTypedDef_live (.viewLen viewValue) [] (.data (.int .i64))
  · intro live
    simpa [Op.uses] using input live
  · simp [Op.origin]
  · simp [Op.SymbolRefsValid]
  · intro _
    exact effectRefinement_empty func target
  · intro _ root member
    cases member
  · intro _ _
    rfl

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

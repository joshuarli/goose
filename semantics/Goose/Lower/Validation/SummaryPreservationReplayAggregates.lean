import Goose.Lower.Validation.SummaryPreservationReplayScalar

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem arrayLiteral {env : PEnv} {ty : Ty} {elements : List Expr}
    {initialSource before after : RState} {sourceRoots : List RootRef}
    {initial : LS} {values : List ValueId}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (elementsReplay : rpExprs env elements initialSource = .ok ((), before))
    (source : rpExpr env (.arrLit ty elements) initialSource = .ok (sourceRoots, after))
    (elementsRun : lowerExprs elements le initial = (values, ls))
    (bounds : ls.cur.isSome = true → ∀ value ∈ values, value < ls.vals.size) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.arrLit ty elements) le initial).2 next ∧
      ((lowerExpr (.arrLit ty elements) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.arrLit ty elements) le initial).2
          (lowerExpr (.arrLit ty elements) le initial).1 sourceRoots (.data ty)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have replay : rpExpr env (.arrLit ty elements) initialSource = .ok ([], before) := by
    simp [rpExpr, elementsReplay, bind, pure, Except.bind, Except.pure, StateT.bind, StateT.pure]
  rw [replay] at source
  cases source
  have whole : lowerExpr (.arrLit ty elements) le initial = Goose.Lower.emitDef (.arrLit ty values) le ls := by
    simp only [lowerExpr, bind_run, elementsRun]
  rw [whole]
  exact ready.emitTypedDef_live (.arrLit ty values) [] (.data ty)
    (by intro live; simpa [Op.uses] using bounds live) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
    (fun _ => effectRefinement_empty func target) (fun _ _ member => by cases member) (fun _ _ => rfl)

theorem structLiteral {env : PEnv} {ty : Ty} {elements : List Expr}
    {initialSource before after : RState} {sourceRoots : List RootRef}
    {initial : LS} {values : List ValueId}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (elementsReplay : rpExprs env elements initialSource = .ok ((), before))
    (source : rpExpr env (.structLit ty elements) initialSource = .ok (sourceRoots, after))
    (elementsRun : lowerExprs elements le initial = (values, ls))
    (bounds : ls.cur.isSome = true → ∀ value ∈ values, value < ls.vals.size) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.structLit ty elements) le initial).2 next ∧
      ((lowerExpr (.structLit ty elements) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.structLit ty elements) le initial).2
          (lowerExpr (.structLit ty elements) le initial).1 sourceRoots (.data ty)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have replay : rpExpr env (.structLit ty elements) initialSource = .ok ([], before) := by
    simp [rpExpr, elementsReplay, bind, pure, Except.bind, Except.pure, StateT.bind, StateT.pure]
  rw [replay] at source
  cases source
  have whole : lowerExpr (.structLit ty elements) le initial = Goose.Lower.emitDef (.structLit ty values) le ls := by
    simp only [lowerExpr, bind_run, elementsRun]
  rw [whole]
  exact ready.emitTypedDef_live (.structLit ty values) [] (.data ty)
    (by intro live; simpa [Op.uses] using bounds live) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
    (fun _ => effectRefinement_empty func target) (fun _ _ member => by cases member) (fun _ _ => rfl)

theorem arrayFill {env : PEnv} {ty : Ty} {element : Expr}
    {initialSource before after : RState} {elementRoots sourceRoots : List RootRef}
    {initial : LS} {value : ValueId}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (elementReplay : rpExpr env element initialSource = .ok (elementRoots, before))
    (source : rpExpr env (.fill ty element) initialSource = .ok (sourceRoots, after))
    (elementRun : lowerExpr element le initial = (value, ls))
    (bound : ls.cur.isSome = true → value < ls.vals.size) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.fill ty element) le initial).2 next ∧
      ((lowerExpr (.fill ty element) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.fill ty element) le initial).2
          (lowerExpr (.fill ty element) le initial).1 sourceRoots (.data ty)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have replay : rpExpr env (.fill ty element) initialSource = .ok ([], before) := by
    simp [rpExpr, elementReplay, bind, pure, Except.bind, Except.pure, StateT.bind, StateT.pure]
  rw [replay] at source
  cases source
  have whole : lowerExpr (.fill ty element) le initial = Goose.Lower.emitDef (.arrFill ty value) le ls := by
    simp only [lowerExpr, bind_run, elementRun]
  rw [whole]
  exact ready.emitTypedDef_live (.arrFill ty value) [] (.data ty)
    (by intro live; simpa [Op.uses] using bound live) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
    (fun _ => effectRefinement_empty func target) (fun _ _ member => by cases member) (fun _ _ => rfl)

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

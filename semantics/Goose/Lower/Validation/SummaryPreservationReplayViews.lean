import Goose.Lower.Validation.SummaryPreservationReplayLiveEmit
import Goose.Lower.Validation.SummaryPreservationRefinedEffects

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem placeView {env : PEnv} {place : Place} {initialSource before after : RState}
    {placeRoots sourceRoots : List RootRef} {initial : LS} {address : ValueId}
    (mutability : Mutability) (element : Ty)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (closed : ParameterRootsClosed func)
    (placeReplay : rpPlace env place initialSource = .ok (placeRoots, before))
    (source : rpView env (.of place) initialSource = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (placeRun : lowerPlace place le initial = (address, ls))
    (input : ls.cur.isSome = true → address < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals address) placeRoots) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerView (.of place) le initial).2 next ∧
      ((lowerView (.of place) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerView (.of place) le initial).2
          (lowerView (.of place) le initial).1 sourceRoots (.view mutability element)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have replay : rpView env (.of place) initialSource = .ok (placeRoots,
      { before with eff := { before.eff with reads := addTargets before.eff.reads (rootsTargets placeRoots) } }) := by
    simp [rpView, placeReplay, addReads, addRoots, bind, pure, modify, Except.bind, Except.pure,
      StateT.bind, StateT.pure, StateT.modifyGet, modifyGet, MonadStateOf.modifyGet]
  rw [replay] at source
  cases source
  let mode : SnapshotMode := match place with | .var _ | .global _ => .owner | _ => .borrowed
  have whole : lowerView (.of place) le initial = Goose.Lower.emitDef (.snapshot mode address) le ls := by
    simp only [lowerView, bind_run, placeRun]
    cases place <;> rfl
  rw [whole]
  apply ready.emitTypedDef_live (.snapshot mode address) placeRoots (.view mutability element)
  · intro live
    simpa [Op.uses] using (input live).1
  · simp [Op.origin]
  · simp [Op.SymbolRefsValid]
  · intro live
    exact (effectStep_snapshot_refines closed (effectRefinement_empty func before.eff) (input live).2).trans wholeEffect
  · intro live
    exact (input live).2
  · simp [VTy.refLike]

theorem valueView {env : PEnv} {expression : Expr} {before after : RState}
    {valueRoots sourceRoots : List RootRef} {initial : LS} {value : ValueId}
    (mutability : Mutability) (element : Ty)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (valueReplay : rpExpr env expression before = .ok (valueRoots, after))
    (source : rpView env (.val expression) before = .ok (sourceRoots, after))
    (valueRun : lowerExpr expression le initial = (value, ls))
    (input : ls.cur.isSome = true → value < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals value) valueRoots) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerView (.val expression) le initial).2 next ∧
      ((lowerView (.val expression) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerView (.val expression) le initial).2
          (lowerView (.val expression) le initial).1 sourceRoots (.view mutability element)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  change rpExpr env expression before = .ok (sourceRoots, after) at source
  rw [valueReplay] at source
  cases source
  have whole : lowerView (.val expression) le initial = Goose.Lower.emitDef (.sliceView value) le ls := by
    simp only [lowerView, bind_run, valueRun]
  rw [whole]
  apply ready.emitTypedDef_live (.sliceView value) valueRoots (.view mutability element)
  · intro live
    simpa [Op.uses] using (input live).1
  · simp [Op.origin]
  · simp [Op.SymbolRefsValid]
  · intro _
    exact effectRefinement_empty func target
  · intro live
    exact (input live).2
  · simp [VTy.refLike]

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

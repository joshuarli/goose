import Goose.Lower.Validation.SummaryPreservationReplayLiveEmit
import Goose.Lower.Validation.SummaryPreservationRefinedEffects

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem localPlace {env : PEnv} {before after : RState} {sourceRoots : List RootRef}
    (variableId : VarId) (mutability : Mutability) (ty : Ty)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : rpPlace env (.var variableId) before = .ok (sourceRoots, after))
    (slotBound : variableId < le.slots.size) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerPlace (.var variableId) le ls).2 next ∧
      ((lowerPlace (.var variableId) le ls).2.cur.isSome = true →
        ReplayValue func next (lowerPlace (.var variableId) le ls).2
          (lowerPlace (.var variableId) le ls).1 sourceRoots (.data (.ref mutability ty))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have sameRoots : sourceRoots = [.local variableId] := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
  subst sourceRoots
  exact ready.emitTypedDef (.slotAddr variableId) [.local variableId] (.data (.ref mutability ty))
    (by simp [Op.uses]) (by simp [Op.origin]) slotBound
    (effectRefinement_empty func target) (RootsRefine.refl _ _) (by simp [VTy.refLike, Ty.isRefLike])

theorem globalPlace {env : PEnv} {before after : RState} {sourceRoots : List RootRef}
    (globalId : GlobalId) (mutability : Mutability) (ty : Ty)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : rpPlace env (.global globalId) before = .ok (sourceRoots, after))
    (globalBound : globalId < le.globals.size) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerPlace (.global globalId) le ls).2 next ∧
      ((lowerPlace (.global globalId) le ls).2.cur.isSome = true →
        ReplayValue func next (lowerPlace (.global globalId) le ls).2
          (lowerPlace (.global globalId) le ls).1 sourceRoots (.data (.ref mutability ty))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have sameRoots : sourceRoots = [.global globalId] := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
  subst sourceRoots
  exact ready.emitTypedDef (.globalAddr globalId) [.global globalId] (.data (.ref mutability ty))
    (by simp [Op.uses]) (by simp [Op.origin]) globalBound
    (effectRefinement_empty func target) (RootsRefine.refl _ _) (by simp [VTy.refLike, Ty.isRefLike])

theorem fieldPlace {env : PEnv} {place : Place} {field : Nat}
    {before after : RState} {ownerRoots sourceRoots : List RootRef}
    {initial : LS} {address : ValueId} (mutability : Mutability) (ty : Ty)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (ownerReplay : rpPlace env place before = .ok (ownerRoots, after))
    (source : rpPlace env (.field place field) before = .ok (sourceRoots, after))
    (ownerRun : lowerPlace place le initial = (address, ls))
    (input : ls.cur.isSome = true → address < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals address) ownerRoots) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerPlace (.field place field) le initial).2 next ∧
      ((lowerPlace (.field place field) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerPlace (.field place field) le initial).2
          (lowerPlace (.field place field) le initial).1 sourceRoots (.data (.ref mutability ty))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  change rpPlace env place before = .ok (sourceRoots, after) at source
  rw [ownerReplay] at source
  cases source
  have whole : lowerPlace (.field place field) le initial = Goose.Lower.emitDef (.fieldAddr address field) le ls := by
    simp only [lowerPlace, bind_run, ownerRun]
  rw [whole]
  apply ready.emitTypedDef_live (.fieldAddr address field) ownerRoots (.data (.ref mutability ty))
  · intro live
    simpa [Op.uses] using (input live).1
  · simp [Op.origin]
  · simp [Op.SymbolRefsValid]
  · intro _
    exact effectRefinement_empty func target
  · intro live
    exact (input live).2
  · simp [VTy.refLike, Ty.isRefLike]


theorem dereferencePlace {env : PEnv} {expression : Expr} {before after : RState}
    {valueRoots sourceRoots : List RootRef} {initial : LS} {value : ValueId}
    (mutability : Mutability) (ty : Ty)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (valueReplay : rpExpr env expression before = .ok (valueRoots, after))
    (source : rpPlace env (.deref expression) before = .ok (sourceRoots, after))
    (valueRun : lowerExpr expression le initial = (value, ls))
    (input : ls.cur.isSome = true → ReplayValue func upper ls value valueRoots (.data (.ref mutability ty))) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerPlace (.deref expression) le initial).2 next ∧
      ((lowerPlace (.deref expression) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerPlace (.deref expression) le initial).2
          (lowerPlace (.deref expression) le initial).1 sourceRoots (.data (.ref mutability ty))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  change rpExpr env expression before = .ok (sourceRoots, after) at source
  rw [valueReplay] at source
  cases source
  simp only [lowerPlace, valueRun]
  exact ⟨upper, ready, input, fun _ _ => rfl⟩

theorem elementPlace {env : PEnv} {view : View} {index : Expr} {origin : OriginId}
    {initialSource viewState before after : RState} {viewRoots indexRoots sourceRoots : List RootRef}
    {initial viewLS : LS} {viewValue indexValue : ValueId}
    (mutability : Mutability) (ty : Ty)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (viewReplay : rpView env view initialSource = .ok (viewRoots, viewState))
    (indexReplay : rpExpr env index viewState = .ok (indexRoots, before))
    (source : rpPlace env (.elem view index origin) initialSource = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (viewRun : lowerView view le initial = (viewValue, viewLS))
    (indexRun : lowerExpr index le viewLS = (indexValue, ls))
    (originBound : origin < le.mod.origins.size)
    (input : ls.cur.isSome = true → viewValue < ls.vals.size ∧ indexValue < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals viewValue) viewRoots) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerPlace (.elem view index origin) le initial).2 next ∧
      ((lowerPlace (.elem view index origin) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerPlace (.elem view index origin) le initial).2
          (lowerPlace (.elem view index origin) le initial).1 sourceRoots (.data (.ref mutability ty))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have replay : rpPlace env (.elem view index origin) initialSource =
      .ok (viewRoots, { before with eff := { before.eff with aborts := true } }) := by
    simp [rpPlace, viewReplay, indexReplay, noteAborts, bind, pure, modify,
      Except.bind, Except.pure, StateT.bind, StateT.pure, StateT.modifyGet, modifyGet, MonadStateOf.modifyGet]
  rw [replay] at source
  cases source
  have whole : lowerPlace (.elem view index origin) le initial =
      Goose.Lower.emitDef (.indexChecked viewValue indexValue (some origin)) le ls := by
    simp only [lowerPlace, bind_run, viewRun, indexRun]
  rw [whole]
  apply ready.emitTypedDef_live (.indexChecked viewValue indexValue (some origin)) viewRoots (.data (.ref mutability ty))
  · intro live
    simpa [Op.uses] using And.intro (input live).1 (input live).2.1
  · simpa [Op.origin] using originBound
  · simp [Op.SymbolRefsValid]
  · intro _
    exact (effectRefinement_noteAborts (effectRefinement_empty func before.eff)).trans wholeEffect
  · intro live
    exact (input live).2.2
  · simp [VTy.refLike, Ty.isRefLike]

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

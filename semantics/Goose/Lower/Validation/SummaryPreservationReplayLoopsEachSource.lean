import Goose.Lower.Validation.SummaryPreservationReplayLoopsEachOps
import Goose.Lower.Validation.SummaryPreservationReplayViews
import Goose.Lower.Validation.DeadFrontier

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

structure ReplayEachSource (func : Func) (upper : Prov) (ls : LS)
    (sampled : Option ValueId × ValueId) (sourceRoots : List RootRef) (element : Ty) : Prop where
  view : ReplayValue func upper ls sampled.2 sourceRoots (.view .readOnly element)
  owner : ∀ address, sampled.1 = some address →
    address < ls.vals.size ∧ RootsRefine func (rootsAt upper.vals address) sourceRoots

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

set_option maxHeartbeats 1200000

theorem eachSource {tenv : TEnv} {env : PEnv} {view : View} {element : Ty} {writable : Bool}
    {start finish : Nat} {before after : RState} {sourceRoots : List RootRef}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (typing : Core.tyView tenv view start = .ok ((element, writable), finish))
    (source : rpView env view before = .ok (sourceRoots, after))
    (closed : ParameterRootsClosed func) (wholeEffect : EffectRefinement func after.eff target)
    (placeStep : ∀ place, view = .of place → ∀ info next sourceAfter placeRoots state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      Core.tyPlace tenv place start = .ok (info, next) →
      rpPlace env place before = .ok (placeRoots, sourceAfter) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots (lowerPlace place le state).2 next ∧
        ((lowerPlace place le state).2.cur.isSome = true →
          (lowerPlace place le state).1 < (lowerPlace place le state).2.vals.size ∧
          RootsRefine func (rootsAt next.vals (lowerPlace place le state).1) placeRoots) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    (expressionStep : ∀ expression, view = .val expression → ∀ type next state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      Core.tyExpr tenv expression start = .ok (type, next) →
      rpExpr env expression before = .ok (sourceRoots, after) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots (lowerExpr expression le state).2 next ∧
        ((lowerExpr expression le state).2.cur.isSome = true →
          (lowerExpr expression le state).1 < (lowerExpr expression le state).2.vals.size ∧
          RootsRefine func (rootsAt next.vals (lowerExpr expression le state).1) sourceRoots) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots (lowerEachSource view le ls).2 next ∧
      ((lowerEachSource view le ls).2.cur.isSome = true →
        ReplayEachSource func next (lowerEachSource view le ls).2 (lowerEachSource view le ls).1 sourceRoots element) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases view with
  | of place =>
    have viewReplay := source
    simp only [Core.tyView] at typing
    obtain ⟨info, next, placeTyped, _⟩ := (st_bind_ok _ _ _ _).mp typing
    simp only [rpView] at source
    obtain ⟨placeRoots, placeState, placeReplay, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, readState, readReplay, source⟩ := (st_bind_ok _ _ _ _).mp source
    have pair := (st_pure_ok _ _ _).mp source
    cases pair
    let placeResult := lowerPlace place le ls
    obtain ⟨placeProv, placeReady, placeValue, placeGrowth⟩ :=
      placeStep place rfl info next placeState sourceRoots ls upper ready placeTyped placeReplay
    obtain ⟨viewProv, viewReady, viewValue, viewGrowth⟩ := placeReady.placeView .readOnly element closed
      placeReplay viewReplay wholeEffect (show lowerPlace place le ls = (placeResult.1, placeResult.2) from rfl) placeValue
    let mode : SnapshotMode := match place with | .var _ | .global _ => .owner | _ => .borrowed
    let sampled := Goose.Lower.emitDef (.snapshot mode placeResult.1) le placeResult.2
    have whole : lowerEachSource (.of place) le ls = ((some placeResult.1, sampled.1), sampled.2) := by
      simp only [lowerEachSource, bind_run, pure_run]
      cases place <;> rfl
    have sameView : lowerView (.of place) le ls = sampled := by
      simp only [lowerView, bind_run]
      cases place <;> rfl
    rw [sameView] at viewReady viewValue
    refine ⟨viewProv, by simpa only [whole] using viewReady, ?_, ?_⟩
    · rw [whole]
      intro live
      refine ⟨viewValue live, ?_⟩
      intro address same
      cases same
      have placeLive := (dead_emitDef (.snapshot mode placeResult.1)).live_before
        (show Goose.Lower.emitDef (.snapshot mode placeResult.1) le placeResult.2 = (sampled.1, sampled.2) from rfl) live
      obtain ⟨bound, refined⟩ := placeValue placeLive
      have beforeBound : placeResult.1 < placeProv.vals.size := by simpa only [placeReady.roots.valueSize] using bound
      refine ⟨Nat.lt_of_lt_of_le bound (advB_emitDef (.snapshot mode placeResult.1) le placeResult.2 sampled.1 sampled.2 rfl).vals, ?_⟩
      rw [viewGrowth placeResult.1 beforeBound]
      exact refined
    · intro index bound
      have placeBound : index < placeProv.vals.size := by
        rw [placeReady.roots.valueSize]
        exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound)
          (advB_lowerPlace place le ls placeResult.1 placeResult.2 rfl).vals
      rw [viewGrowth index placeBound, placeGrowth index bound]
  | val expression =>
    simp only [Core.tyView] at typing
    obtain ⟨type, next, expressionTyped, _⟩ := (st_bind_ok _ _ _ _).mp typing
    let expressionResult := lowerExpr expression le ls
    obtain ⟨expressionProv, expressionReady, expressionValue, expressionGrowth⟩ :=
      expressionStep expression rfl type next ls upper ready expressionTyped source
    obtain ⟨viewProv, viewReady, viewValue, viewGrowth⟩ := expressionReady.valueView .readOnly element
      source source (show lowerExpr expression le ls = (expressionResult.1, expressionResult.2) from rfl) expressionValue
    let sampled := Goose.Lower.emitDef (.sliceView expressionResult.1) le expressionResult.2
    have whole : lowerEachSource (.val expression) le ls = ((none, sampled.1), sampled.2) := by
      simp only [lowerEachSource, bind_run, pure_run]
      rfl
    have sameView : lowerView (.val expression) le ls = sampled := by
      simp only [lowerView, bind_run]
      rfl
    rw [sameView] at viewReady viewValue
    refine ⟨viewProv, by simpa only [whole] using viewReady, ?_, ?_⟩
    · rw [whole]
      intro live
      exact ⟨viewValue live, by intro address impossible; cases impossible⟩
    · intro index bound
      have expressionBound : index < expressionProv.vals.size := by
        rw [expressionReady.roots.valueSize]
        exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound)
          (advB_lowerExpr expression le ls expressionResult.1 expressionResult.2 rfl).vals
      rw [viewGrowth index expressionBound, expressionGrowth index bound]

end ReplayBuilder

#print axioms ReplayBuilder.eachSource

end Goose.Lower.Validation.SummaryPreservation

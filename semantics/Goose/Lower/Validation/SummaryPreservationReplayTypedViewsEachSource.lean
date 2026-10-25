import Goose.Lower.Validation.SummaryPreservationReplayTypedViews
import Goose.Lower.Validation.SummaryPreservationReplayLoopsEachSource

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

set_option maxHeartbeats 1200000

theorem typedEachSource {typingEnv : TEnv} {env : PEnv} {view : View} {element : Ty} {writable : Bool}
    {start finish : Nat} {before after : RState} {sourceRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {ls : LS} {upper : Prov}
    (typing : tyView typingEnv view start = .ok ((element, writable), finish))
    (source : rpView env view before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target)
    (closed : ParameterRootsClosed (lowerContextAt env.mod env.ctx env.impl))
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) ls upper)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerEachSource view (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2)
    (placeChild : ∀ place, view = .of place → PlaceReplayAt typingEnv env results vt target scopeCount place ls upper)
    (expressionChild : ∀ expression, view = .val expression → ExpressionReplayAt typingEnv env results vt target scopeCount expression ls upper) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerEachSource view (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 next ∧
      ((lowerEachSource view (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        ReplayEachSource (lowerContextAt env.mod env.ctx env.impl) next
          (lowerEachSource view (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2
          (lowerEachSource view (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 sourceRoots element) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old := by
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  have nativeView : NativeRows vt (lowerView view le ls).2 := by cases view <;> exact native
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
    have placeEffect := effectRefinement_before_of_replay (PMono.addReads sourceRoots)
      (PMonoRebinds.addReads sourceRoots) (PFlagsMono.addReads sourceRoots) readReplay wholeEffect
    have viewWhole : lowerView (.of place) le ls = Goose.Lower.emitDef
        (.snapshot (match place with | .var _ | .global _ => .owner | _ => .borrowed) placeResult.1) le placeResult.2 := by
      simp only [lowerView, bind_run]
      cases place <;> rfl
    have childNative : NativeRows vt placeResult.2 := by
      apply nativeView.of_prefix
      rw [viewWhole]
      exact types_emitDef _ le placeResult.2 _ _ rfl
    obtain ⟨placeProv, placeReady, placeValue, placeGrowth⟩ :=
      placeChild place rfl info start next before placeState sourceRoots placeTyped placeReplay placeEffect ready generated childNative
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
    refine ⟨viewProv, ?_, ?_, ?_⟩
    · rw [whole]
      exact viewReady
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
    have childNative : NativeRows vt expressionResult.2 := by
      apply nativeView.of_prefix
      exact types_emitDef (.sliceView expressionResult.1) le expressionResult.2 _ _ rfl
    obtain ⟨expressionProv, expressionReady, typedValue, expressionGrowth⟩ :=
      expressionChild expression rfl type start next before after sourceRoots expressionTyped source wholeEffect ready generated childNative
    have expressionValue := fun live => And.intro (typedValue live).bound (typedValue live).refined
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
    refine ⟨viewProv, ?_, ?_, ?_⟩
    · rw [whole]
      exact viewReady
    · rw [whole]
      intro live
      exact ⟨viewValue live, by intro address impossible; cases impossible⟩
    · intro index bound
      have expressionBound : index < expressionProv.vals.size := by
        rw [expressionReady.roots.valueSize]
        exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound)
          (advB_lowerExpr expression le ls expressionResult.1 expressionResult.2 rfl).vals
      rw [viewGrowth index expressionBound, expressionGrowth index bound]

#print axioms typedEachSource

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

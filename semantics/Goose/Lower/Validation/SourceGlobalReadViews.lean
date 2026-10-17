import Goose.Lower.Validation.SourceGlobalReadContracts
import Goose.Lower.Validation.SummaryPreservationReplayViews

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedGlobalView {typingEnv : TEnv} {env : PEnv} {view : View} {info : Ty × Bool}
    {start finish : Nat} {before after : RState} {sourceRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff}
    {scopeCount : Nat} {ls : LS} {upper : Prov}
    (source : tyView typingEnv view start = .ok (info, finish))
    (replayed : rpView env view before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (closed : ParameterRootsClosed func)
    (ready : ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots ls upper)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) ls).2)
    (placeChild : ∀ place, view = .of place → GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount place ls upper)
    (expressionChild : ∀ expression, view = .val expression → GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount expression ls upper) :
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) ls).2 next ∧
      ((lowerView view (lowerEnv env.mod env.impl.vars returnTypes) ls).2.cur.isSome = true →
        ReplayValue func next
          (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) ls).2
          (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) ls).1 sourceRoots (.view .readOnly info.1)) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old := by
  let le := lowerEnv env.mod env.impl.vars returnTypes
  cases view with
  | of place =>
    obtain ⟨placeInfo, placeFinish, placeTyped, _⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨placeRoots, placeState, placeReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replayed
    have placeEffect := effectRefinement_before_of_replay
      (PMono.bind (PMono.addReads placeRoots) (fun _ => PMono.pure placeRoots))
      (PMonoRebinds.bind (PMonoRebinds.addReads placeRoots) (fun _ => PMonoRebinds.pure placeRoots))
      (PFlagsMono.bind (PFlagsMono.addReads placeRoots) (fun _ => PFlagsMono.pure placeRoots)) tail wholeEffect
    let lowered := lowerPlace place le ls
    have whole : lowerView (.of place) le ls = Goose.Lower.emitDef
        (.snapshot (match place with | .var _ | .global _ => .owner | _ => .borrowed) lowered.1) le lowered.2 := by
      simp only [lowerView, bind_run]
      cases place <;> rfl
    have childNative : NativeRows vt lowered.2 := by
      apply native.of_prefix
      rw [whole]
      exact types_emitDef _ le lowered.2 _ _ rfl
    obtain ⟨middle, middleReady, input, retained⟩ := placeChild place rfl placeInfo start placeFinish before placeState placeRoots
      placeTyped placeReplay placeEffect ready generated childNative
    obtain ⟨next, nextReady, value, nextRetained⟩ := middleReady.placeView .readOnly info.1 closed
      placeReplay replayed wholeEffect (rfl : lowerPlace place le ls = lowered) input
    refine ⟨next, nextReady, value, ?_⟩
    have advanced := advB_lowerPlace place le ls lowered.1 lowered.2 rfl
    intro old bound
    have middleBound : old < middle.vals.size := by
      rw [middleReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) advanced.vals
    rw [nextRetained old middleBound, retained old bound]
  | val expression =>
    obtain ⟨childType, childFinish, childTyped, _⟩ := (st_bind_ok _ _ _ _).mp source
    let lowered := lowerExpr expression le ls
    have whole : lowerView (.val expression) le ls = Goose.Lower.emitDef (.sliceView lowered.1) le lowered.2 := by
      simp only [lowerView, bind_run]
      rfl
    have childNative : NativeRows vt lowered.2 := by
      apply native.of_prefix
      rw [whole]
      exact types_emitDef _ le lowered.2 _ _ rfl
    obtain ⟨middle, middleReady, input, retained⟩ := expressionChild expression rfl childType start childFinish before after sourceRoots
      childTyped replayed wholeEffect ready generated childNative
    obtain ⟨next, nextReady, value, nextRetained⟩ := middleReady.valueView .readOnly info.1 replayed replayed
      (rfl : lowerExpr expression le ls = lowered) (fun live => ⟨(input live).bound, (input live).refined⟩)
    refine ⟨next, nextReady, value, ?_⟩
    have advanced := advB_lowerExpr expression le ls lowered.1 lowered.2 rfl
    intro old bound
    have middleBound : old < middle.vals.size := by
      rw [middleReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) advanced.vals
    rw [nextRetained old middleBound, retained old bound]

#print axioms typedGlobalView

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

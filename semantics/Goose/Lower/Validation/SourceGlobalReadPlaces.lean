import Goose.Lower.Validation.SourceGlobalReadContracts
import Goose.Lower.Validation.SummaryPreservationReplayPlaces
import Goose.Lower.Validation.SourceRootShapeReads

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

set_option maxHeartbeats 1200000

theorem typedGlobalPlace {typingEnv : TEnv} {env : PEnv} {place : Place}
    {info : PlaceInfo} {start finish : Nat} {before after : RState} {sourceRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff}
    {scopeCount : Nat} {ls : LS} {upper : Prov}
    (tables : SourceRootTables typingEnv env)
    (variables : typingEnv.vars = #[])
    (source : tyPlace typingEnv place start = .ok (info, finish))
    (replayed : rpPlace env place before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (ready : ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots ls upper)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) ls).2)
    (placeChild : ∀ owner field, place = .field owner field →
      GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount owner ls upper)
    (viewChild : ∀ view index origin, place = .elem view index origin →
      GlobalViewReplayAt typingEnv env results vt func returnTypes slots target scopeCount view ls upper)
    (expressionChild : ∀ expression state provenance,
      (place = .deref expression ∧ state = ls) ∨
        (∃ view origin, place = .elem view expression origin ∧
          state = (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) ls).2) →
      GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount expression state provenance) :
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) ls).2 next ∧
      ((lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) ls).2.cur.isSome = true →
        (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) ls).1 <
          (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) ls).2.vals.size ∧
        RootsRefine func
          (rootsAt next.vals (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) ls).1) sourceRoots) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old := by
  let le := lowerEnv env.mod env.impl.vars returnTypes
  cases place with
  | var variableId =>
    obtain ⟨localVar, next, lookup, _⟩ := (st_bind_ok _ _ _ _).mp source
    have row := (varOf_ok _ _ _ _).mp lookup |>.2.1
    simp [variables] at row
  | global globalId =>
    have lookup : ∃ global, typingEnv.mod.globals[globalId]? = some global := by
      by_cases visible : globalId < typingEnv.globalLimit
      · cases row : typingEnv.mod.globals[globalId]? with
        | some global => exact ⟨global, rfl⟩
        | none =>
          simp only [tyPlace, if_pos visible, row] at source
          exact (rej_ok _ _ _ _).mp source |>.elim
      · simp only [tyPlace, if_neg visible] at source
        exact (rej_ok _ _ _ _).mp source |>.elim
    obtain ⟨global, row⟩ := lookup
    have globalBound : globalId < le.globals.size := by
      simpa [le, lowerEnv, tables.moduleEq] using (Array.getElem?_eq_some_iff.mp row).1
    obtain ⟨next, nextReady, value, retained⟩ := ready.globalPlace globalId .readOnly info.ty replayed globalBound
    exact ⟨next, nextReady, fun live => ⟨(value live).bound, (value live).refined⟩, retained⟩
  | field owner field =>
    obtain ⟨ownerInfo, ownerFinish, ownerTyped, _⟩ := (st_bind_ok _ _ _ _).mp source
    let lowered := lowerPlace owner le ls
    have whole : lowerPlace (.field owner field) le ls = Goose.Lower.emitDef (.fieldAddr lowered.1 field) le lowered.2 := by
      simp only [lowerPlace, bind_run]
      rfl
    have childNative : NativeRows vt lowered.2 := by
      apply native.of_prefix
      rw [whole]
      exact types_emitDef _ le lowered.2 _ _ rfl
    obtain ⟨middle, middleReady, input, retained⟩ := placeChild owner field rfl ownerInfo start ownerFinish
      before after sourceRoots ownerTyped replayed wholeEffect ready generated childNative
    obtain ⟨next, nextReady, value, nextRetained⟩ := middleReady.fieldPlace (place := owner) (field := field) (initial := ls) .readOnly info.ty
      (show rpPlace env owner before = .ok (sourceRoots, after) from replayed) replayed
      (rfl : lowerPlace owner le ls = lowered) input
    refine ⟨next, nextReady, fun live => ⟨(value live).bound, (value live).refined⟩, ?_⟩
    have advanced := advB_lowerPlace owner le ls lowered.1 lowered.2 rfl
    intro old bound
    have middleBound : old < middle.vals.size := by
      rw [middleReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) advanced.vals
    rw [nextRetained old middleBound, retained old bound]
  | deref expression =>
    cases special : sliceRefTy typingEnv expression with
    | none =>
      obtain ⟨mutability, childFinish, childTyped⟩ := tyPlace_deref_child special source
      obtain ⟨next, nextReady, value, retained⟩ := expressionChild expression ls upper (Or.inl ⟨rfl, rfl⟩)
        (.ref mutability info.ty) start childFinish before after sourceRoots childTyped replayed wholeEffect ready generated native
      exact ⟨next, nextReady, fun live => ⟨(value live).bound, (value live).refined⟩, retained⟩
    | some type =>
      cases expression with
      | read owner =>
        cases owner with
        | var variableId =>
          obtain ⟨localVar, row, localType, _⟩ := sliceRefTy_variable_row special
          simp [variables] at row
        | _ => simp [sliceRefTy] at special
      | _ => simp [sliceRefTy] at special
  | elem view index origin =>
    obtain ⟨viewStart, viewFinish, indexFinish, writable, integer, viewTyped, indexTyped⟩ := tyPlace_elem_children source
    obtain ⟨viewRoots, viewState, viewReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨indexRoots, indexState, indexReplay, tail⟩ := (st_bind_ok _ _ _ _).mp tail
    have indexEffect := effectRefinement_before_of_replay
      (PMono.bind PMono.noteAborts (fun _ => PMono.pure viewRoots))
      (PMonoRebinds.bind (by unfold noteAborts; exact PMonoRebinds.modify _ (fun _ _ member => member)) (fun _ => PMonoRebinds.pure viewRoots))
      (PFlagsMono.bind (by unfold noteAborts; exact PFlagsMono.modify _ (fun _ => ⟨fun _ => rfl, fun h => h⟩)) (fun _ => PFlagsMono.pure viewRoots)) tail wholeEffect
    have viewEffect := effectRefinement_before_expression indexReplay indexEffect
    let loweredView := lowerView view le ls
    let loweredIndex := lowerExpr index le loweredView.2
    have whole : lowerPlace (.elem view index origin) le ls =
        Goose.Lower.emitDef (.indexChecked loweredView.1 loweredIndex.1 (some origin)) le loweredIndex.2 := by
      simp only [lowerPlace, bind_run]
      rfl
    have indexNative : NativeRows vt loweredIndex.2 := by
      apply native.of_prefix
      rw [whole]
      exact types_emitDef _ le loweredIndex.2 _ _ rfl
    have viewNative : NativeRows vt loweredView.2 := indexNative.of_prefix (types_lowerExpr index le loweredView.2 _ _ rfl)
    obtain ⟨viewProv, viewReady, viewValue, viewRetained⟩ := viewChild view index origin rfl
      (info.ty, writable) viewStart viewFinish before viewState viewRoots viewTyped viewReplay viewEffect ready generated viewNative
    have viewGenerated := generated.lowerView view (rfl : lowerView view le ls = loweredView)
    obtain ⟨indexProv, indexReady, indexValue, indexRetained⟩ := expressionChild index loweredView.2 viewProv
      (Or.inr ⟨view, origin, rfl, rfl⟩) (.int integer) viewFinish indexFinish viewState indexState indexRoots
      indexTyped indexReplay indexEffect viewReady viewGenerated indexNative
    have originBound : origin < le.mod.origins.size := by
      obtain ⟨_, _, originChecked, _⟩ := (st_bind_ok _ _ _ _).mp source
      have bound := (checkOrg_ok _ _ _ _).mp originChecked |>.1
      simpa only [le, lowerEnv, tables.moduleEq] using bound
    have viewAdv := advB_lowerView view le ls loweredView.1 loweredView.2 rfl
    have indexAdv := advB_lowerExpr index le loweredView.2 loweredIndex.1 loweredIndex.2 rfl
    obtain ⟨next, nextReady, value, nextRetained⟩ := indexReady.elementPlace .readOnly info.ty viewReplay indexReplay replayed
      wholeEffect (rfl : lowerView view le ls = loweredView) (rfl : lowerExpr index le loweredView.2 = loweredIndex) originBound
      (by
        intro live
        have viewLive := (dead_lowerExpr index).live_before (rfl : lowerExpr index le loweredView.2 = loweredIndex) live
        have viewResult := viewValue viewLive
        have oldView : loweredView.1 < viewProv.vals.size := by simpa only [viewReady.roots.valueSize] using viewResult.bound
        refine ⟨Nat.lt_of_lt_of_le viewResult.bound indexAdv.vals, (indexValue live).bound, ?_⟩
        rw [indexRetained loweredView.1 oldView]
        exact viewResult.refined)
    refine ⟨next, nextReady, fun live => ⟨(value live).bound, (value live).refined⟩, ?_⟩
    intro old bound
    have viewBound : old < viewProv.vals.size := by
      rw [viewReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) viewAdv.vals
    have indexBound : old < indexProv.vals.size := by
      rw [indexReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [viewReady.roots.valueSize] using viewBound) indexAdv.vals
    rw [nextRetained old indexBound, indexRetained old viewBound, viewRetained old bound]

#print axioms typedGlobalPlace

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessConsumed
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessReadLocal
import Goose.Lower.Validation.SummaryPreservationReplayPlaces
import Goose.Lower.Validation.SourceRootShapeReads

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

set_option maxHeartbeats 1600000

theorem occurrenceReplay_global_place {typingEnv : TEnv} {env : PEnv} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} (place : Place)
    (tables : SourceRootTables typingEnv env) (variables : typingEnv.vars = #[])
    (placeChild : ∀ owner field, place = .field owner field → ∀ initial upper,
      GlobalPlaceOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets owner initial upper)
    (viewChild : ∀ view index origin, place = .elem view index origin → ∀ initial upper,
      GlobalViewOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets view initial upper)
    (expressionChild : ∀ expression state provenance,
      place = .deref expression ∨ (∃ view origin, place = .elem view expression origin) →
      GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets expression state provenance) :
    ∀ initial upper, GlobalPlaceOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets place initial upper := by
  intro initial upper here info start finish before after sourceRoots typed replayed wholeEffect ready sites targets generated native metadata continuation
  let le := lowerEnv env.mod env.impl.vars returnTypes
  cases place with
  | var variableId =>
    obtain ⟨localVar, next, lookup, _⟩ := (st_bind_ok _ _ _ _).mp typed
    have row := (varOf_ok _ _ _ _).mp lookup |>.2.1
    have slotBound : variableId < le.slots.size := by
      simpa [le, lowerEnv, tables.variablesEq] using (Array.getElem?_eq_some_iff.mp row).1
    obtain ⟨next, nextReady, value, retained⟩ := ready.localPlace variableId .readOnly info.ty replayed slotBound
    have growth := accessRootsGrowth ready nextReady (advB_lowerPlace (.var variableId) le initial _ _ rfl).vals
    refine ⟨next, nextReady, fun live => ⟨(value live).bound, (value live).refined⟩, retained, ?_, ?_⟩
    · exact emitsOnly_emitDef rfl (by simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands])
    · exact sites.emitDef rfl growth retained
  | global globalId =>
    have lookup : ∃ global, typingEnv.mod.globals[globalId]? = some global := by
      by_cases visible : globalId < typingEnv.globalLimit
      · cases row : typingEnv.mod.globals[globalId]? with
        | some global => exact ⟨global, rfl⟩
        | none =>
          simp only [tyPlace, if_pos visible, row] at typed
          exact (rej_ok _ _ _ _).mp typed |>.elim
      · simp only [tyPlace, if_neg visible] at typed
        exact (rej_ok _ _ _ _).mp typed |>.elim
    obtain ⟨global, row⟩ := lookup
    have globalBound : globalId < le.globals.size := by
      simpa [le, lowerEnv, tables.moduleEq] using (Array.getElem?_eq_some_iff.mp row).1
    obtain ⟨next, nextReady, value, retained⟩ := ready.globalPlace globalId .readOnly info.ty replayed globalBound
    have growth := accessRootsGrowth ready nextReady (advB_lowerPlace (.global globalId) le initial _ _ rfl).vals
    refine ⟨next, nextReady, fun live => ⟨(value live).bound, (value live).refined⟩, retained, ?_, ?_⟩
    · exact emitsOnly_emitDef rfl (by simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands])
    · exact sites.emitDef rfl growth retained
  | field owner field =>
    obtain ⟨ownerInfo, ownerFinish, ownerTyped, _⟩ := (st_bind_ok _ _ _ _).mp typed
    let lowered := lowerPlace owner le initial
    have whole : lowerPlace (.field owner field) le initial = Goose.Lower.emitDef (.fieldAddr lowered.1 field) le lowered.2 := by
      simp only [lowerPlace, bind_run]
      rfl
    have childNative : NativeRows vt lowered.2 := by
      apply native.of_prefix
      rw [whole]
      exact types_emitDef _ le lowered.2 _ _ rfl
    have childMetadata := metadata.of_advance (before := lowered.2) (by
      rw [whole]
      exact advB_emitDef _ le lowered.2 _ _ rfl)
    have childContinuation := continuation.of_advance (before := lowered.2) (by
      rw [whole]
      exact advB_emitDef _ le lowered.2 _ _ rfl)
    obtain ⟨middle, middleReady, input, retained, childLedger, childSites⟩ := placeChild owner field rfl initial upper
      (accessChildPresent here 0 rfl) ownerInfo start ownerFinish
      before after sourceRoots ownerTyped replayed wholeEffect ready sites targets generated childNative childMetadata childContinuation
    obtain ⟨next, nextReady, value, nextRetained⟩ := middleReady.fieldPlace (place := owner) (field := field) (initial := initial) .readOnly info.ty
      (show rpPlace env owner before = .ok (sourceRoots, after) from replayed) replayed
      (rfl : lowerPlace owner le initial = lowered) input
    have suffixRun : emitDef (.fieldAddr lowered.1 field) le lowered.2 = lowerPlace (.field owner field) le initial := whole.symm
    have growth := accessRootsGrowth middleReady nextReady (adv_emitDef suffixRun).vals
    have suffix : OccurrenceLedger env (.place (.field owner field)) (func) vt next
        lowered.2 (lowerPlace (.field owner field) le initial).2 :=
      emitsOnly_emitDef suffixRun (by simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands])
    refine ⟨next, nextReady, fun live => ⟨(value live).bound, (value live).refined⟩, ?_,
      ((childLedger.retained growth nextRetained).underRoot (accessChildNode 0 rfl)).trans suffix,
      childSites.emitDef suffixRun growth nextRetained⟩
    have advanced := advB_lowerPlace owner le initial lowered.1 lowered.2 rfl
    intro old bound
    have middleBound : old < middle.vals.size := by
      rw [middleReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) advanced.vals
    rw [nextRetained old middleBound, retained old bound]
  | deref expression =>
    cases special : sliceRefTy typingEnv expression with
    | none =>
      obtain ⟨mutability, childFinish, childTyped⟩ := tyPlace_deref_child special typed
      obtain ⟨next, nextReady, value, retained, childLedger, childSites⟩ := expressionChild expression initial upper
        (Or.inl rfl) (accessChildPresent here 0 rfl)
        (.ref mutability info.ty) start childFinish before after sourceRoots childTyped replayed wholeEffect ready sites targets generated native metadata continuation
      exact ⟨next, nextReady, fun live => ⟨(value live).bound, (value live).refined⟩, retained,
        childLedger.underRoot (accessChildNode 0 rfl), childSites⟩
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
    obtain ⟨viewStart, viewFinish, indexFinish, writable, integer, viewTyped, indexTyped⟩ := tyPlace_elem_children typed
    obtain ⟨viewRoots, viewState, viewReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨indexRoots, indexState, indexReplay, tail⟩ := (st_bind_ok _ _ _ _).mp tail
    have indexEffect := effectRefinement_before_of_replay
      (PMono.bind PMono.noteAborts (fun _ => PMono.pure viewRoots))
      (PMonoRebinds.bind (by unfold noteAborts; exact PMonoRebinds.modify _ (fun _ _ member => member)) (fun _ => PMonoRebinds.pure viewRoots))
      (PFlagsMono.bind (by unfold noteAborts; exact PFlagsMono.modify _ (fun _ => ⟨fun _ => rfl, fun h => h⟩)) (fun _ => PFlagsMono.pure viewRoots)) tail wholeEffect
    have viewEffect := effectRefinement_before_expression indexReplay indexEffect
    let loweredView := lowerView view le initial
    let loweredIndex := lowerExpr index le loweredView.2
    have whole : lowerPlace (.elem view index origin) le initial =
        Goose.Lower.emitDef (.indexChecked loweredView.1 loweredIndex.1 (some origin)) le loweredIndex.2 := by
      simp only [lowerPlace, bind_run]
      rfl
    have indexNative : NativeRows vt loweredIndex.2 := by
      apply native.of_prefix
      rw [whole]
      exact types_emitDef _ le loweredIndex.2 _ _ rfl
    have indexMetadata := metadata.of_advance (before := loweredIndex.2) (by
      rw [whole]
      exact advB_emitDef _ le loweredIndex.2 _ _ rfl)
    have indexContinuation := continuation.of_advance (before := loweredIndex.2) (by
      rw [whole]
      exact advB_emitDef _ le loweredIndex.2 _ _ rfl)
    have viewMetadata := indexMetadata.of_advance (advB_lowerExpr index le loweredView.2 _ _ rfl)
    have viewContinuation := indexContinuation.of_advance (advB_lowerExpr index le loweredView.2 _ _ rfl)
    have viewNative : NativeRows vt loweredView.2 := indexNative.of_prefix (types_lowerExpr index le loweredView.2 _ _ rfl)
    obtain ⟨viewProv, viewReady, viewValue, viewRetained, viewLedger, viewSites⟩ := viewChild view index origin rfl initial upper
      (accessChildPresent here 0 rfl) (info.ty, writable) viewStart viewFinish before viewState viewRoots viewTyped viewReplay viewEffect ready sites targets generated viewNative viewMetadata viewContinuation
    have viewGenerated := generated.lowerView view (rfl : lowerView view le initial = loweredView)
    obtain ⟨indexProv, indexReady, indexValue, indexRetained, indexLedger, indexSites⟩ := expressionChild index loweredView.2 viewProv
      (Or.inr ⟨view, origin, rfl⟩) (accessChildPresent here 1 rfl) (.int integer) viewFinish indexFinish viewState indexState indexRoots
      indexTyped indexReplay indexEffect viewReady viewSites (targets.mono viewLedger.extension) viewGenerated indexNative indexMetadata indexContinuation
    have originBound : origin < le.mod.origins.size := by
      obtain ⟨_, _, originChecked, _⟩ := (st_bind_ok _ _ _ _).mp typed
      have bound := (checkOrg_ok _ _ _ _).mp originChecked |>.1
      simpa only [le, lowerEnv, tables.moduleEq] using bound
    have viewAdv := advB_lowerView view le initial loweredView.1 loweredView.2 rfl
    have indexAdv := advB_lowerExpr index le loweredView.2 loweredIndex.1 loweredIndex.2 rfl
    obtain ⟨next, nextReady, value, nextRetained⟩ := indexReady.elementPlace .readOnly info.ty viewReplay indexReplay replayed
      wholeEffect (rfl : lowerView view le initial = loweredView) (rfl : lowerExpr index le loweredView.2 = loweredIndex) originBound
      (by
        intro live
        have viewLive := (dead_lowerExpr index).live_before (rfl : lowerExpr index le loweredView.2 = loweredIndex) live
        have viewResult := viewValue viewLive
        have oldView : loweredView.1 < viewProv.vals.size := by simpa only [viewReady.roots.valueSize] using viewResult.bound
        refine ⟨Nat.lt_of_lt_of_le viewResult.bound indexAdv.vals, (indexValue live).bound, ?_⟩
        rw [indexRetained loweredView.1 oldView]
        exact viewResult.refined)
    have suffixRun : emitDef (.indexChecked loweredView.1 loweredIndex.1 (some origin)) le loweredIndex.2 =
        lowerPlace (.elem view index origin) le initial := whole.symm
    have growth := accessRootsGrowth indexReady nextReady (adv_emitDef suffixRun).vals
    have viewGrowth := accessRootsGrowth viewReady indexReady indexAdv.vals
    have environment : lowerEnv typingEnv.mod typingEnv.vars returnTypes = le := by
      rw [← tables.moduleEq, ← tables.variablesEq]
    have scalar (live : loweredIndex.2.cur.isSome = true) : valRefLike vt loweredIndex.1 = false :=
      indexNative.scalar_expression viewGenerated indexTyped (by rw [environment]) live rfl
    have suffix : OccurrenceLedger env (.place (.elem view index origin)) (func) vt next
        loweredIndex.2 (lowerPlace (.elem view index origin) le initial).2 := by
      apply accessEmitDefinition suffixRun
      intro live
      refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store (by intros; intro same; cases same), ?_⟩
      · intro address member reference
        simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with viewAddress | indexAddress
        · subst address
          have viewLive := (dead_lowerExpr index).live_before (rfl : lowerExpr index le loweredView.2 = loweredIndex) live
          have oldBound : loweredView.1 < viewProv.vals.size := by
            rw [viewReady.roots.valueSize]
            exact (viewValue viewLive).bound
          have indexBound := Nat.lt_of_lt_of_le oldBound viewGrowth
          apply accessOperandView (accessChildNode 0 rfl) viewReplay (Nat.lt_of_lt_of_le indexBound growth)
          rw [nextRetained loweredView.1 indexBound, indexRetained loweredView.1 oldBound]
          exact (viewValue viewLive).refined
        · subst address
          rw [scalar live] at reference
          cases reference
      · intro value address same; cases same
      · intro value callee args origin same; cases same
      · intro address member mutability payload reference
        simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · have viewLive := (dead_lowerExpr index).live_before (rfl : lowerExpr index le loweredView.2 = loweredIndex) live
          exact False.elim (sourceView_not_reference tables viewNative generated viewTyped (rfl : lowerView view le initial = loweredView) viewLive mutability payload reference)
        · exact False.elim (nativeScalar_not_reference (scalar live) mutability payload reference)
    refine ⟨next, nextReady, fun live => ⟨(value live).bound, (value live).refined⟩, ?_,
      (((viewLedger.retained viewGrowth indexRetained).retained growth nextRetained).underRoot
        (accessChildNode 0 rfl)).trans
          (((indexLedger.retained growth nextRetained).underRoot (accessChildNode 1 rfl)).trans suffix),
      indexSites.emitDef suffixRun growth nextRetained⟩
    intro old bound
    have viewBound : old < viewProv.vals.size := by
      rw [viewReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) viewAdv.vals
    have indexBound : old < indexProv.vals.size := by
      rw [indexReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [viewReady.roots.valueSize] using viewBound) indexAdv.vals
    rw [nextRetained old indexBound, indexRetained old viewBound, viewRetained old bound]

end Goose.Lower.Validation.ReplacementContentFlowSource

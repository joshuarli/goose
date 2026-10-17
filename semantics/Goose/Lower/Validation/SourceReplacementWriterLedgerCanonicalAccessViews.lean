import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessConsumed
import Goose.Lower.Validation.SummaryPreservationReplayViews
import Goose.Lower.Validation.SummaryPreservationSourceContextEnvironment

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open ReplacementContentFlowSource Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}


theorem canonical_occurrenceReplay_view {typingEnv : TEnv} {env : PEnv} {context : ContextId}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} (view : View)
    (source : SourceContextEnvironment typingEnv env context)
    (placeChild : ∀ place, view = .of place → ∀ initial upper,
      CanonicalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets place initial upper)
    (expressionChild : ∀ expression, view = .val expression → ∀ initial upper,
      CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper) :
    ∀ initial upper, CanonicalViewOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets view initial upper := by
  intro initial upper here sourceCursor info start finish before after sourceRoots typed replayed wholeEffect ready sites targets generated native metadata continuation
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let func := lowerContextAt env.mod env.ctx env.impl
  cases view with
  | of place =>
    obtain ⟨placeInfo, placeFinish, placeTyped, _⟩ := (st_bind_ok _ _ _ _).mp typed
    obtain ⟨placeRoots, placeState, placeReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replayed
    have placeEffect := effectRefinement_before_of_replay
      (PMono.bind (PMono.addReads placeRoots) (fun _ => PMono.pure placeRoots))
      (PMonoRebinds.bind (PMonoRebinds.addReads placeRoots) (fun _ => PMonoRebinds.pure placeRoots))
      (PFlagsMono.bind (PFlagsMono.addReads placeRoots) (fun _ => PFlagsMono.pure placeRoots)) tail wholeEffect
    let lowered := lowerPlace place le initial
    let mode : SnapshotMode := match place with | .var _ | .global _ => .owner | _ => .borrowed
    have whole : lowerView (.of place) le initial = emitDef (.snapshot mode lowered.1) le lowered.2 := by
      simp only [lowerView, bind_run]
      cases place <;> rfl
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
    obtain ⟨middle, middleReady, input, retained, childLedger, childSites⟩ :=
      placeChild place rfl initial upper (accessChildPresent here 0 rfl) (by
        obtain ⟨path, located⟩ := sourceCursor
        exact ⟨path ++ [0], located.child rfl⟩) placeInfo start placeFinish
        before placeState placeRoots placeTyped placeReplay placeEffect ready sites targets generated childNative childMetadata childContinuation
    obtain ⟨next, nextReady, value, nextRetained⟩ := middleReady.placeView .readOnly info.1 source.parameters
      placeReplay replayed wholeEffect (rfl : lowerPlace place le initial = lowered) input
    have suffixRun : emitDef (.snapshot mode lowered.1) le lowered.2 = lowerView (.of place) le initial := whole.symm
    have growth := accessRootsGrowth middleReady nextReady (adv_emitDef suffixRun).vals
    have suffix : OccurrenceLedger env (.view (.of place)) func vt next lowered.2
        (lowerView (.of place) le initial).2 := by
      apply accessEmitDefinition suffixRun
      intro live
      refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store (by intros; intro same; cases same), ?_⟩
      · intro address member reference
        simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
        subst address
        have bound : lowered.1 < middle.vals.size := by
          rw [middleReady.roots.valueSize]
          exact (input live).1
        apply accessOperandPlace (accessChildNode 0 rfl) placeReplay (Nat.lt_of_lt_of_le bound growth)
        rw [nextRetained lowered.1 bound]
        exact (input live).2
      · intro value address same; cases same
      · intro value callee args origin same; cases same
      · intro address member mutability payload reference
        simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
        subst address
        have bound : lowered.1 < middle.vals.size := by
          rw [middleReady.roots.valueSize]
          exact (input live).1
        apply ConsumedReferenceOccurrence.place _ env _ _ _ _ _ rfl (accessChildNode 0 rfl) placeReplay (Nat.lt_of_lt_of_le bound growth)
        rw [nextRetained lowered.1 bound]
        exact (input live).2
    refine ⟨next, nextReady, value, ?_, ?_, childSites.emitDef suffixRun growth nextRetained⟩
    · intro old bound
      have middleBound := Nat.lt_of_lt_of_le bound (accessRootsGrowth ready middleReady
        (advB_lowerPlace place le initial lowered.1 lowered.2 rfl).vals)
      exact (nextRetained old middleBound).trans (retained old bound)
    · exact ((childLedger.retained growth nextRetained).underRoot (accessChildNode 0 rfl)).trans suffix
  | val expression =>
    obtain ⟨childType, childFinish, childTyped, _⟩ := (st_bind_ok _ _ _ _).mp typed
    let lowered := lowerExpr expression le initial
    have whole : lowerView (.val expression) le initial = emitDef (.sliceView lowered.1) le lowered.2 := by
      simp only [lowerView, bind_run]
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
    obtain ⟨middle, middleReady, input, retained, childLedger, childSites⟩ :=
      expressionChild expression rfl initial upper (accessChildPresent here 0 rfl) (by
        obtain ⟨path, located⟩ := sourceCursor
        exact ⟨path ++ [0], located.child rfl⟩) childType start childFinish
        before after sourceRoots childTyped replayed wholeEffect ready sites targets generated childNative childMetadata childContinuation
    obtain ⟨next, nextReady, value, nextRetained⟩ := middleReady.valueView .readOnly info.1 replayed replayed
      (rfl : lowerExpr expression le initial = lowered) (fun live => ⟨(input live).bound, (input live).refined⟩)
    have suffixRun : emitDef (.sliceView lowered.1) le lowered.2 = lowerView (.val expression) le initial := whole.symm
    have growth := accessRootsGrowth middleReady nextReady (adv_emitDef suffixRun).vals
    have suffix : OccurrenceLedger env (.view (.val expression)) func vt next lowered.2
        (lowerView (.val expression) le initial).2 := by
      apply accessEmitDefinition suffixRun
      intro live
      refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store (by intros; intro same; cases same), ?_⟩
      · intro address member reference
        simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
        subst address
        have bound : lowered.1 < middle.vals.size := by
          rw [middleReady.roots.valueSize]
          exact (input live).bound
        apply accessOperandExpression (accessChildNode 0 rfl) replayed (Nat.lt_of_lt_of_le bound growth)
        rw [nextRetained lowered.1 bound]
        exact (input live).refined
      · intro value address same; cases same
      · intro value callee args origin same; cases same
      · intro address member mutability payload reference
        simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
        subst address
        have row := sourceExpressionNative source.tables childNative generated childTyped (rfl : lowerExpr expression le initial = lowered) live
        exact False.elim (nativeData_not_reference row (sourceValueView_not_reference typed childTyped) mutability payload reference)
    refine ⟨next, nextReady, value, ?_, ?_, childSites.emitDef suffixRun growth nextRetained⟩
    · intro old bound
      have middleBound := Nat.lt_of_lt_of_le bound (accessRootsGrowth ready middleReady
        (advB_lowerExpr expression le initial lowered.1 lowered.2 rfl).vals)
      exact (nextRetained old middleBound).trans (retained old bound)
    · exact ((childLedger.retained growth nextRetained).underRoot (accessChildNode 0 rfl)).trans suffix

end Goose.Lower.Validation.SourceReplacementWriterLedger

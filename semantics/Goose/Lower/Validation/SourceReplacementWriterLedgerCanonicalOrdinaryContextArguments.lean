import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsPhysicalPlaces
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsBorrow
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsGlobal
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalOrdinaryArguments
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalAccessReadLocal
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalCallBorrow

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}
  {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat}
  {siteRoot anchor : DemandNode} {siteTargets : List BlockId}

theorem canonical_typedContextPhysicalArgumentOccurrence
    (source : SourceContextEnvironment typingEnv env context)
    (argument : Arg)
    (expressionChild : ∀ expression, argument = .byVal expression → ∀ state provenance,
      CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target
        scopeCount siteRoot siteTargets expression state provenance)
    (placeChild : ∀ mutability place, argument = .byRef mutability place → ∀ state provenance,
      CanonicalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target
        scopeCount siteRoot siteTargets place state provenance) :
    ∀ initial upper, CanonicalPhysicalArgumentOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt
      (lowerContextAt env.mod env.ctx env.impl) env.impl.results.toList
      (typedContextSlotUpper env.mod env.ctx env.impl) target scopeCount siteRoot siteTargets anchor argument initial upper := by
  intro initial upper anchored argumentPath sourceCursor start finish before after sourceRoots typed replay wholeEffect
    ready sites targets generated native metadata continuation
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  cases argument with
  | byVal expression =>
    obtain ⟨next, completed, returned, retained, ledger, nextSites⟩ :=
      canonical_typedGlobalArgumentOccurrence (.byVal expression)
        (fun child same state provenance => expressionChild child (by simpa using same) state provenance)
        (fun mutability place same state provenance =>
          placeChild mutability place (by simpa using same) state provenance)
        initial upper anchored argumentPath sourceCursor start finish before after sourceRoots typed replay wholeEffect
        ready sites targets generated native metadata continuation
    exact ⟨next, completed, returned, retained, ledger, nextSites,
      by intro live mutability place impossible shape; cases impossible⟩
  | byRef mutability place =>
    by_cases shaped : ∃ index, place = .var index ∨
        (place = .deref (.read (.var index)) ∧ env.isRefSliceVar index = true ∧ (env.cont index).isSome = true)
    · obtain ⟨info, placeTyped⟩ := typed
      have checkpoint : ∃ middle,
          ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target le scopeCount
            (typedContextSlotUpper env.mod env.ctx env.impl) (lowerPlace place le initial).2 middle ∧
          ((lowerPlace place le initial).2.cur.isSome = true →
            (lowerPlace place le initial).1 < (lowerPlace place le initial).2.vals.size ∧
            GIR.RootsRefine (lowerContextAt env.mod env.ctx env.impl)
              (rootsAt middle.vals (lowerPlace place le initial).1) sourceRoots ∧
            ReadAddressPhysical env place (rootsAt middle.vals (lowerPlace place le initial).1)) ∧
          (∀ old, old < upper.vals.size → rootsAt middle.vals old = rootsAt upper.vals old) ∧
          OccurrenceLedger env (.place place) (lowerContextAt env.mod env.ctx env.impl) vt middle
            initial (lowerPlace place le initial).2 ∧
          CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le
            (lowerPlace place le initial).2 (lowerContextAt env.mod env.ctx env.impl) vt middle := by
        obtain ⟨index, localPlace | ⟨contentsPlace, reference, contents⟩⟩ := shaped
        · subst place
          obtain ⟨middle, completed, value, retained, ledger, _⟩ :=
            contextArgumentVariablePlace source placeTyped replay ready sites.toOld
          have growth : upper.vals.size ≤ middle.vals.size :=
            accessRootsGrowth ready completed (advB_lowerPlace (.var index) le initial _ _ rfl).vals
          exact ⟨middle, completed, fun live => ⟨(value live).1, (value live).2.1,
            .local index rfl (value live).2.2⟩, retained, ledger,
            sites.emitDef (by rfl) growth retained⟩
        · subst place
          cases row : env.impl.vars[index]? with
          | none => simp [PEnv.isRefSliceVar, row] at reference
          | some localVar =>
            have refSlice : localVar.ty.isRefSlice = true := by
              simpa only [PEnv.isRefSliceVar, row] using reference
            obtain ⟨middle, completed, value, retained, ledger, _⟩ :=
              contextArgumentReferencePlace source row refSlice contents replay ready sites.toOld
                (metadata.of_advance (by
                  exact advB_borrowTo mutability
                    (lowerPlace (.deref (.read (.var index))) le initial).1
                    le (lowerPlace (.deref (.read (.var index))) le initial).2 _ _ rfl))
            exact ⟨middle, completed, fun live => ⟨(value live).1, (value live).2.1,
              .contents index rfl reference (value live).2.2⟩, retained, ledger,
              canonical_accessLocalReadSites ready completed sites retained⟩
      obtain ⟨middle, middleReady, address, middleRoots, placeLedger, middleSites⟩ := checkpoint
      obtain ⟨next, nextReady, returned, nextRoots, borrowedLedger, nextSites, physical⟩ :=
        canonical_argumentBorrowOccurrence (root := anchor) mutability info.ty
          (lowerPlace place le initial).1 sourceRoots middleReady middleSites
          (fun live => ⟨(address live).1, (address live).2.1⟩)
      let first := lowerPlace place le initial
      let borrowed := borrowTo mutability first.1 le first.2
      have whole : lowerArg (.byRef mutability place) le initial = borrowed := by
        simp only [lowerArg, bind_run]
        rfl
      have ghostGrowth : middle.vals.size ≤ next.vals.size := by
        rw [middleReady.roots.valueSize, nextReady.roots.valueSize]
        exact (advB_borrowTo mutability first.1 le first.2 _ _ rfl).vals
      obtain ⟨childPath, childDemand⟩ := argumentPath
      obtain ⟨cursorPath, childSource⟩ := sourceCursor
      have firstFinalLedger := (placeLedger.underRoot childDemand).retained ghostGrowth nextRoots
      dsimp only [le] at whole
      rw [whole]
      refine ⟨next, nextReady, ?_, ?_, firstFinalLedger.trans borrowedLedger, nextSites, ?_⟩
      · intro live
        have value := returned live
        refine ⟨value.bound, value.refined, childPath, .place place, before, sourceRoots, after,
          childDemand, SourceNodeRoots.place rfl replay, ?_, value.refined⟩
        rw [nextReady.roots.valueSize]
        exact value.bound
      · intro index bound
        have growth : upper.vals.size ≤ middle.vals.size := by
          rw [ready.roots.valueSize, middleReady.roots.valueSize]
          exact (advB_lowerPlace place le initial first.1 first.2 rfl).vals
        exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots index bound)
      · intro live actualMutability actualPlace same shape
        cases same
        rw [physical live]
        exact (address ((dead_borrowTo mutability first.1).live_before rfl live)).2.2
    · obtain ⟨next, completed, returned, retained, ledger, nextSites⟩ :=
        canonical_typedGlobalArgumentOccurrence (.byRef mutability place)
          (fun expression same state provenance =>
            expressionChild expression (by simpa using same) state provenance)
          (fun actualMutability actualPlace same state provenance =>
            placeChild actualMutability actualPlace (by simpa using same) state provenance)
          initial upper anchored argumentPath sourceCursor start finish before after sourceRoots typed replay wholeEffect
        ready sites targets generated native metadata continuation
      refine ⟨next, completed, returned, retained, ledger, nextSites, ?_⟩
      intro live actualMutability actualPlace same shape
      cases same
      exact (shaped shape).elim

#print axioms canonical_typedContextPhysicalArgumentOccurrence

end Goose.Lower.Validation.SourceReplacementWriterLedger

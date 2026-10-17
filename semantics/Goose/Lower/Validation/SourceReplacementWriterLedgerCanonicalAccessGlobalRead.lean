import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames
import Goose.Lower.Validation.SourceRootShapeReads
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalAccessReadRaw
import Goose.Lower.Validation.SummaryPreservationReplayContentReadNestedOrigins
import Goose.Lower.Validation.SummaryPreservationReplayScalarReadOrigins
import Goose.Lower.Validation.SummaryPreservationReplayTypedRead
import Goose.Lower.Validation.SourceGlobalReadShape
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open ReplacementContentFlowSource Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}


theorem canonical_occurrenceReplay_global_read {typingEnv : TEnv} {env : PEnv} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {place : Place}
    (checked : SourceReadableEnvironment typingEnv) (tables : SourceRootTables typingEnv env)
    (variables : typingEnv.vars = #[]) (parameters : ParameterRootsClosed func)
    (child : ∀ initial upper, CanonicalGlobalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets place initial upper) :
    ∀ initial upper, CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets (.read place) initial upper := by
  intro initial upper here sourceCursor type start finish before after roots typed replay ceiling ready sites targets generated native metadata continuation
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let addressed := lowerPlace place le initial
  have nonref := source_empty_read_nonref checked variables typed
  have inactive := ReplayBuilder.nonrefRead_record_inactive typed nonref
    (show le.vars = typingEnv.vars from by simpa [le, lowerEnv] using tables.variablesEq)
  have outerRun : emitDef (.load addressed.1) le addressed.2 = lowerExpr (.read place) le initial := by
    rw [lowerExpr_read_run]
    simp only [inactive]
    rfl
  have lowerEnvironment : lowerEnv typingEnv.mod typingEnv.vars returnTypes = le := by
    rw [← tables.moduleEq, ← tables.variablesEq]
  have resultTag (live : (lowerExpr (.read place) le initial).2.cur.isSome = true) :
      vt[(lowerExpr (.read place) le initial).1]? = some (some (.data type)) := by
    apply native.expression generated typed
    · rw [lowerEnvironment]
    · exact live
  have resultType (active : addressed.2.cur.isSome = true) :
      vt[addressed.2.vals.size]? = some (some (.data type)) := by
    have live := (congrArg Option.isSome (accessEmitCurrent outerRun)).trans active
    have fresh : (lowerExpr (.read place) le initial).1 = addressed.2.vals.size := by
      rw [← outerRun]
      cases current : addressed.2.cur with
      | none => simp [current] at active
      | some block => rw [emitDef_run _ _ current]
    simpa only [fresh] using resultTag live
  obtain ⟨info, counter, placeTyped, _⟩ := tyExpr_read_place typed
  obtain ⟨placeRoots, placeAfter, placeReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  have effectBound := effectRefinement_before_of_replay
    (PMono.bind (PMono.addReads placeRoots) (fun _ => PMono.readRoots env place))
    (PMonoRebinds.bind (PMonoRebinds.addReads placeRoots) (fun _ => PMonoRebinds.readRoots env place))
    (PFlagsMono.bind (PFlagsMono.addReads placeRoots) (fun _ => PFlagsMono.readRoots env place)) tail ceiling
  obtain ⟨middle, middleReady, input, middleRoots, ledger, childSites⟩ := child initial upper
    (accessChildPresent here 0 rfl) (by
        obtain ⟨path, located⟩ := sourceCursor
        exact ⟨path ++ [0], located.child rfl⟩) info start counter before placeAfter placeRoots placeTyped placeReplay
    effectBound ready sites targets generated (native.of_prefix (types_emitDef (.load addressed.1) le addressed.2 _ _ outerRun))
        (metadata.of_advance (adv_emitDef outerRun))
        (continuation.of_advance (adv_emitDef outerRun))
  obtain ⟨next, completed, value, retained, origins⟩ := middleReady.scalarReadWithOrigins type nonref parameters
    placeReplay replay ceiling (placeRun := rfl) input resultType inactive
  have growth := accessRootsGrowth middleReady completed (adv_emitDef outerRun).vals
  have suffix : OccurrenceLedger env (.expression (.read place)) (func) vt next
      addressed.2 (lowerExpr (.read place) le initial).2 := by
    apply accessLoadLedger (result := (lowerExpr (.read place) le initial).1) outerRun (.here _) placeReplay replay
    · intro active
      have live := (congrArg Option.isSome (accessEmitCurrent outerRun)).trans active
      obtain ⟨bound, refined⟩ := origins live
      exact ⟨by simpa only [completed.roots.valueSize] using bound,
        by simpa only [completed.roots.valueSize] using (value live).bound, refined, (value live).refined⟩
    · intro active reference
      have live := (congrArg Option.isSome (accessEmitCurrent outerRun)).trans active
      have tag := resultTag live
      simp only [valRefLike, tag, VTy.refLike, nonref] at reference
      cases reference
  refine ⟨next, completed, value, ?_,
    ((ledger.retained growth retained).underRoot (accessChildNode 0 rfl)).trans suffix,
    childSites.emitDef outerRun growth retained⟩
  intro old bound
  have firstGrowth := accessRootsGrowth ready middleReady (advB_lowerPlace place le initial _ _ rfl).vals
  exact (retained old (Nat.lt_of_lt_of_le bound firstGrowth)).trans (middleRoots old bound)

#print axioms canonical_occurrenceReplay_global_read

end Goose.Lower.Validation.SourceReplacementWriterLedger

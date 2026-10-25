import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessReadRaw
import Goose.Lower.Validation.SummaryPreservationReplayContentReadNestedOrigins
import Goose.Lower.Validation.SummaryPreservationReplayScalarReadOrigins
import Goose.Lower.Validation.SummaryPreservationReplayTypedRead
import Goose.Lower.Validation.SourceReadablePlaceShape

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem occurrenceReplay_read {typingEnv : TEnv} {env : PEnv} {context : ContextId}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {place : Place}
    (source : SourceContextEnvironment typingEnv env context)
    (child : ∀ initial upper, PlaceOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets place initial upper) :
    ∀ initial upper, ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets (.read place) initial upper := by
  intro initial upper here type start finish before after roots typed replay ceiling ready sites targets generated native metadata continuation
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let addressed := lowerPlace place le initial
  have lowerEnvironment : lowerEnv typingEnv.mod typingEnv.vars env.impl.results.toList = le := by
    rw [← source.tables.moduleEq, ← source.tables.variablesEq]
  have resultTag (live : (lowerExpr (.read place) le initial).2.cur.isSome = true) :
      vt[(lowerExpr (.read place) le initial).1]? = some (some (.data type)) := by
    apply native.expression generated typed
    · rw [lowerEnvironment]
    · exact live
  have resultType (active : addressed.2.cur.isSome = true) :
      vt[addressed.2.vals.size]? = some (some (.data type)) := by
    have live : (lowerExpr (.read place) le initial).2.cur.isSome = true := by
      rw [ReplayBuilder.readCurrent_eq]
      exact (congrArg Option.isSome (accessEmitCurrent (rfl : emitDef (.load addressed.1) le addressed.2 = _))).trans active
    have fresh : (lowerExpr (.read place) le initial).1 = addressed.2.vals.size := by
      rw [ReplayBuilder.readValue_eq]
      cases current : addressed.2.cur with
      | none => simp [current] at active
      | some block => rw [emitDef_run _ _ current]
    simpa only [fresh] using resultTag live
  by_cases reference : type.isRefLike = true
  · rcases source_read_expression_shape source.readable typed reference with
      ⟨index, localVar, rfl, variableRow, rfl⟩ |
      ⟨index, localVar, mu, sliceMu, element, rfl, variableRow, localType, rfl, elementFlat⟩
    · have actualRow : env.impl.vars[index]? = some localVar := by
        simpa only [source.tables.variablesEq] using variableRow
      obtain ⟨next, completed, value, retained, origins, physical⟩ := ready.acceptedLocalReadWithOrigins
        source.accepted source.contextRow source.implementationRow actualRow replay
        (by intro _ nonref; rw [reference] at nonref; cases nonref) metadata
      exact ⟨next, completed, fun live => (value live).1, retained,
        accessLocalReadLedger (.here _) replay completed.roots.valueSize (fun live => (value live).1) origins physical,
        accessLocalReadSites ready completed sites retained⟩
    · have actualRow : env.impl.vars[index]? = some localVar := by
        simpa only [source.tables.variablesEq] using variableRow
      have refSlice : localVar.ty.isRefSlice = true := by simp [localType, Ty.isRefSlice, elementFlat]
      obtain ⟨param, parameter, identity, _⟩ := accepted_refSlice_parameter source.accepted source.implementationRow actualRow refSlice
      have parameterVariable : env.impl.vars[param.var]? = some localVar := by simpa only [identity] using actualRow
      have sourceParam : rpExpr env (.read (.deref (.read (.var param.var)))) before = .ok (roots, after) := by
        simpa only [identity] using replay
      let loaded := lowerExpr (.read (.var param.var)) le initial
      have nestedRun : emitDef (.load loaded.1) le loaded.2 =
          lowerExpr (.read (.deref (.read (.var param.var)))) le initial := rfl
      have innerLive (active : initial.cur.isSome = true) : loaded.2.cur.isSome = true := by
        rw [ReplayBuilder.readCurrent_eq]
        exact (congrArg Option.isSome ((accessEmitCurrent (rfl : emitDef (.load (lowerPlace (.var param.var) le initial).1) le
          (lowerPlace (.var param.var) le initial).2 = _)).trans
          (accessEmitCurrent (rfl : emitDef (.slotAddr param.var) le initial = lowerPlace (.var param.var) le initial)))).trans active
      have addressTag (active : initial.cur.isSome = true) : vt[loaded.1]? = some (some (.data localVar.ty)) := by
        have nativeParam : NativeRows vt (lowerExpr (.read (.deref (.read (.var param.var)))) le initial).2 := by
          simpa only [identity] using native
        have innerNative := nativeParam.of_prefix (types_emitDef (.load loaded.1) le loaded.2 _ _ nestedRun)
        simpa only [loaded, identity] using innerNative.local_read parameterVariable (innerLive active)
      have sliceTag (active : initial.cur.isSome = true) : vt[loaded.2.vals.size]? =
          some (some (.data (.slice sliceMu element))) := by
        have resultTypeParam := resultType
        change (lowerExpr (.read (.var index)) le initial).2.cur.isSome = true → _ at resultTypeParam
        simpa only [addressed, lowerPlace, loaded, identity] using resultTypeParam (by simpa only [loaded, identity] using innerLive active)
      obtain ⟨next, completed, value, retained, origins, innerOrigins, physical⟩ := ready.contentReadWithNestedOrigins
        source.accepted source.contextRow source.implementationRow parameter parameterVariable refSlice
        sourceParam ceiling addressTag sliceTag (by simpa only [identity] using metadata)
      have fullLive (active : loaded.2.cur.isSome = true) :
          (lowerExpr (.read (.deref (.read (.var param.var)))) le initial).2.cur.isSome = true :=
        (congrArg Option.isSome (accessEmitCurrent nestedRun)).trans active
      have innerLedger : OccurrenceLedger env (.expression (.read (.deref (.read (.var param.var)))))
          (lowerContextAt env.mod env.ctx env.impl) vt next initial loaded.2 := by
        apply accessLocalReadLedgerRaw (path := [0, 0])
          ((DemandNodeAt.here _).snoc 0 rfl |>.snoc 0 rfl)
        · intro active
          obtain ⟨_, _, _, _, innerReplay, _, _, _⟩ := innerOrigins (fullLive active)
          exact ⟨_, innerReplay⟩
        · intro active
          obtain ⟨_, _, _, _, _, _, _, refined⟩ := innerOrigins (fullLive active)
          refine ⟨?_, refined⟩
          rw [completed.roots.valueSize]
          exact Nat.lt_of_lt_of_le (value_lowerExpr (.read (.var param.var)) le initial _ _ rfl active)
            (adv_emitDef nestedRun).vals
        · intro active
          obtain ⟨placeRoots, placeAfter, _, placeReplay, _, bound, refined, _⟩ := innerOrigins (fullLive active)
          exact ⟨placeRoots, placeAfter, placeReplay, by simpa only [completed.roots.valueSize] using bound, refined⟩
        · intro active
          exact (physical (fullLive active)).2.2
      have suffix : OccurrenceLedger env (.expression (.read (.deref (.read (.var param.var)))))
          (lowerContextAt env.mod env.ctx env.impl) vt next loaded.2
          (lowerExpr (.read (.deref (.read (.var param.var)))) le initial).2 := by
        apply accessEmitDefinition (value := (lowerExpr (.read (.deref (.read (.var param.var)))) le initial).1) nestedRun
        intro active
        obtain ⟨placeRoots, placeAfter, placeReplay, addressBound, addressRefined⟩ := origins (fullLive active)
        change loaded.1 < _ at addressBound
        have valueBound := (value (fullLive active)).bound
        refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store (by intros; intro same; cases same), ?_⟩
        · intro address member reference
          simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
          subst address
          exact accessOperandPlace (accessChildNode 0 rfl) placeReplay
            (by simpa only [completed.roots.valueSize] using addressBound) addressRefined
        · intro result address same reference
          cases same
          exact ⟨env, [], .deref (.read (.var param.var)), before, placeRoots, placeAfter, roots, after,
            rfl, .here _, placeReplay, sourceParam,
            by simpa only [completed.roots.valueSize] using addressBound,
            by simpa only [completed.roots.valueSize] using valueBound,
            addressRefined, (value (fullLive active)).refined,
            .contents param.var rfl (physical (fullLive active)).1 (physical (fullLive active)).2.1⟩
        · intro result callee args origin same; cases same
        · intro address member mutability payload reference
          simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
          subst address
          exact .place _ env _ _ _ _ _ rfl (accessChildNode 0 rfl) placeReplay
            (by simpa only [completed.roots.valueSize] using addressBound) addressRefined
      have package := And.intro completed (And.intro value (And.intro retained
        (And.intro (innerLedger.trans suffix) (accessNestedReadSites ready completed sites retained))))
      exact ⟨next, by simpa only [identity] using package⟩
  · have nonref : type.isRefLike = false := by cases row : type.isRefLike <;> simp_all
    have inactive := ReplayBuilder.nonrefRead_record_inactive typed nonref
      (show le.vars = typingEnv.vars from by simpa [le, lowerEnv] using source.tables.variablesEq)
    have outerRun : emitDef (.load addressed.1) le addressed.2 = lowerExpr (.read place) le initial := by
      rw [lowerExpr_read_run]
      simp only [inactive]
      rfl
    obtain ⟨info, counter, placeTyped, _⟩ := tyExpr_read_place typed
    obtain ⟨placeRoots, placeAfter, placeReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
    have effectBound := effectRefinement_before_of_replay
      (PMono.bind (PMono.addReads placeRoots) (fun _ => PMono.readRoots env place))
      (PMonoRebinds.bind (PMonoRebinds.addReads placeRoots) (fun _ => PMonoRebinds.readRoots env place))
      (PFlagsMono.bind (PFlagsMono.addReads placeRoots) (fun _ => PFlagsMono.readRoots env place)) tail ceiling
    obtain ⟨middle, middleReady, input, middleRoots, ledger, childSites⟩ := child initial upper
      (accessChildPresent here 0 rfl) info start counter before placeAfter placeRoots placeTyped placeReplay
      effectBound ready sites targets generated (native.of_prefix (types_emitDef (.load addressed.1) le addressed.2 _ _ outerRun))
        (metadata.of_advance (adv_emitDef outerRun))
        (continuation.of_advance (adv_emitDef outerRun))
    obtain ⟨next, completed, value, retained, origins⟩ := middleReady.scalarReadWithOrigins type nonref source.parameters
      placeReplay replay ceiling (placeRun := rfl) input resultType inactive
    have growth := accessRootsGrowth middleReady completed (adv_emitDef outerRun).vals
    have suffix : OccurrenceLedger env (.expression (.read place)) (lowerContextAt env.mod env.ctx env.impl) vt next
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

#print axioms occurrenceReplay_read

end Goose.Lower.Validation.ReplacementContentFlowSource

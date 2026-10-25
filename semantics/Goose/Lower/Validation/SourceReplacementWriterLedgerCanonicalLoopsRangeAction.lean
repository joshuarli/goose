import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalLoopsRangeSteps
import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsRangeControl

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open ReplacementContentFlowSource Goose.Core Goose.GIR SummaryPreservation

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}

open SummaryPreservation.ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
  {env : PEnv} {root siteRoot : DemandNode} {siteTargets : List BlockId}

theorem canonical_loopRangeOccurrence (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (sites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le ls func vt upper)
    (targetBounds : ReplacementTargetsBound siteTargets ls)
    (expected : List RootRef) (type : IntTy) (counter bound : ValueId) (header : BlockId)
    (body : Nat → BlockId → B ValueId)
    (live : ls.cur.isSome = true) (headerBound : header < ls.blocks.size)
    (counterBound : counter < ls.vals.size) (boundBound : bound < ls.vals.size)
    (counterScalar : rootsAt upper.vals counter = [])
    (counterType : valRefLike vt counter = false) (boundType : valRefLike vt bound = false)
    (headerIncluded : header ∈ siteTargets)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerRange type counter bound header body le ls).2)
    (projects : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func
      (lowerRange type counter bound header body le ls).2)
    (continuation : NativeBuilderContinuation func (lowerRange type counter bound header body le ls).2)
    (bodyAdv : ∀ depth exit, AdvB (body depth exit))
    (bodyStep : ∀ provenance,
      let compared := Goose.Lower.emitDef (.cmp .lt type counter bound) le ls
      let split := fork compared.1 le compared.2
      let started := nativeRangeBody type counter bound le ls
      ReplayBuilder module results vt func target le scopeCount slots started provenance →
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot (split.1.2 :: siteTargets) le started func vt provenance →
      ReplacementTargetsBound (split.1.2 :: siteTargets) started →
      GeneratedBuilderState started → NativeRows vt (body compared.2.stack.length split.1.2 le started).2 →
      header < started.blocks.size → split.1.2 < started.blocks.size → counter < started.vals.size →
      rootsAt provenance.vals counter = [] →
      (∀ old, old < upper.vals.size → rootsAt provenance.vals old = rootsAt upper.vals old) →
      SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func (body compared.2.stack.length split.1.2 le started).2 →
      NativeBuilderContinuation func (body compared.2.stack.length split.1.2 le started).2 →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (body compared.2.stack.length split.1.2 le started).2 next ∧
        (∀ old, old < provenance.vals.size → rootsAt next.vals old = rootsAt provenance.vals old) ∧
        ReturnBoundsPreserved expected started provenance (body compared.2.stack.length split.1.2 le started).2 next ∧
        OccurrenceLedger env root func vt next started (body compared.2.stack.length split.1.2 le started).2 ∧
        CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot (split.1.2 :: siteTargets) le (body compared.2.stack.length split.1.2 le started).2 func vt next) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots (lowerRange type counter bound header body le ls).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved expected ls upper (lowerRange type counter bound header body le ls).2 next ∧
      OccurrenceLedger env root func vt next ls (lowerRange type counter bound header body le ls).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le (lowerRange type counter bound header body le ls).2 func vt next := by
  let compare := Goose.Lower.emitDef (.cmp .lt type counter bound) le ls
  obtain ⟨compareProv, compareReady, compareValue, compareGrowth⟩ := ready.emitTypedDef (.cmp .lt type counter bound) [] (.data .bool)
    (by simp [Op.uses, counterBound, boundBound]) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
    (effectRefinement_empty func target) (fun _ member => by cases member) (fun _ => rfl)
  have compareAdv := advB_emitDef (.cmp .lt type counter bound) le ls compare.1 compare.2 rfl
  have compareGenerated := generated.emitDef _ (rfl : Goose.Lower.emitDef (.cmp .lt type counter bound) le ls = compare)
  have compareLive : compare.2.cur.isSome = true := by
    cases current : ls.cur with
    | none => simp [current] at live
    | some block => simpa [compare, emitDef_run _ _ current, current]
  have headerStill := Nat.lt_of_lt_of_le headerBound compareAdv.ext.1
  have counterStill := Nat.lt_of_lt_of_le counterBound compareAdv.vals
  have counterOld : counter < upper.vals.size := by simpa only [ready.roots.valueSize] using counterBound
  have counterRoots := (compareGrowth counter counterOld).trans counterScalar
  have nativeLoop : NativeRows vt (Goose.Lower.loopBody compare.1 body (rangeBack type counter header) le compare.2).2 := native
  have backReturns : ReturnFrameRun (rangeBack type counter header) :=
    .of_absence (fun _ => ReturnFrames.returnAbsent_rangeBack type counter header)
  have compareSites := sites.emitDef_replay ready compareReady rfl compareGrowth
  have compareLedger : OccurrenceLedger env root func vt compareProv ls compare.2 := by
    apply occurrence_emitDef_live rfl
    intro active
    apply canonical_scalarDef _ _ ?_ (by intro address same; cases same) (by intro callee args origin same; cases same)
    intro operand member
    simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact counterType
    · exact boundType
  obtain ⟨next, nextReady, growth, transfer, suffixLedger, finalSites⟩ := canonical_loopBodyOccurrence
    (root := root) compareReady compareSites (targetBounds.mono compareAdv.ext) expected compare.1 (compareValue compareLive).bound
    compareLive body (rangeBack type counter header) compareGenerated nativeLoop projects continuation bodyAdv (advB_rangeBack _ _ _)
    (types_rangeBack _ _ _) backReturns
    (by
      dsimp only
      intro stateReady stateSites stateBounds stateGenerated stateNative exitBound blocks values bodyProjects bodyContinuation
      exact bodyStep compareProv stateReady stateSites stateBounds stateGenerated stateNative (Nat.lt_of_lt_of_le headerStill blocks) exitBound
        (Nat.lt_of_lt_of_le counterStill values) counterRoots compareGrowth bodyProjects bodyContinuation)
    (by
      intro state provenance stateReady stateSites blocks values priorRoots
      obtain ⟨next, completed, retained⟩ := stateReady.loopRangeBack type counter header
        (Nat.lt_of_lt_of_le headerStill blocks) (Nat.lt_of_lt_of_le counterStill values)
      have ghostGrowth : provenance.vals.size ≤ next.vals.size := by
        rw [stateReady.roots.valueSize, completed.roots.valueSize]
        exact (advB_rangeBack type counter header le state _ _ rfl).vals
      exact ⟨next, completed, retained, canonical_occurrenceLedger_rangeBack type counter header counterType le state _ _ rfl,
        canonical_occurrenceSites_rangeBack stateSites type counter header (List.mem_cons_of_mem _ headerIncluded) ghostGrowth retained⟩)
  have compareReturns : ReturnMembershipFrame ls compare.2 :=
    ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_emitDef _) le ls compare.1 compare.2 rfl
  have compareTransfer : ReturnBoundsPreserved expected ls upper compare.2 compareProv :=
    .frame ready.symbols ready.roots.valueSize compareGrowth compareReturns
  refine ⟨next, nextReady, ?_, compareTransfer.trans transfer, ?_, finalSites⟩
  · intro old bound
    have compareBound : old < compareProv.vals.size := by
      rw [compareReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) compareAdv.vals
    rw [growth old compareBound, compareGrowth old bound]
  · have nextGrowth : compareProv.vals.size ≤ next.vals.size := by
      rw [compareReady.roots.valueSize, nextReady.roots.valueSize]
      exact (advB_loopBody compare.1 bodyAdv (advB_rangeBack _ _ _) le compare.2 _ _ rfl).vals
    exact (compareLedger.retained nextGrowth growth).trans suffixLedger

#print axioms canonical_loopRangeOccurrence

end Goose.Lower.Validation.SourceReplacementWriterLedger

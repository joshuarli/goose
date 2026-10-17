import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLoopsRangeAction
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLoopsEachOps
import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsEachControl

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation
open SummaryPreservation.ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
  {env : PEnv} {root siteRoot : DemandNode} {siteTargets : List BlockId}

theorem loopEachOccurrence (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (sites : OccurrenceSitesBuilder env siteRoot siteTargets le ls func vt upper)
    (targetBounds : ReplacementTargetsBound siteTargets ls)
    (expected : List RootRef) (regrow : Bool) (owner : Option ValueId) (sampled counter view : ValueId) (header : BlockId)
    (element : Ty) (sourceRoots : List RootRef) (body : Nat → BlockId → B ValueId)
    (sourceView : ViewOccurrenceSource env root sourceRoots)
    (ownerSource : regrow = true → ∃ place, sourceView.view = .of place) (headerIncluded : header ∈ siteTargets)
    (sampleType : regrow = false → valRefLike vt sampled = false)
    (live : ls.cur.isSome = true) (headerBound : header < ls.blocks.size)
    (counterBound : counter < ls.vals.size) (counterScalar : rootsAt upper.vals counter = [])
    (closed : ParameterRootsClosed func)
    (input : regrow = true → owner.getD 0 < ls.vals.size ∧ Goose.GIR.RootsRefine func (rootsAt upper.vals (owner.getD 0)) sourceRoots)
    (reads : regrow = true → ∀ item ∈ func.storageTargets (rootsTargets sourceRoots), item ∈ func.storageTargets target.reads)
    (sample : regrow = false → ReplayValue func upper ls sampled [] (.data (.int .i64)))
    (viewBound : view < ls.vals.size) (viewRefined : Goose.GIR.RootsRefine func (rootsAt upper.vals view) sourceRoots)
    (viewRow : ∃ mu, ls.vals[view]? = some (some (.view mu element)))
    (counterRow : ls.vals[counter]? = some (some (.data (.int .i64))))
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerEach regrow owner sampled header counter body le ls).2)
    (projects : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func
      (lowerEach regrow owner sampled header counter body le ls).2)
    (continuation : NativeBuilderContinuation func (lowerEach regrow owner sampled header counter body le ls).2)
    (bodyAdv : ∀ depth exit, AdvB (body depth exit))
    (bodyTypes : ∀ depth exit, TypeRun (body depth exit))
    (bodyStep : ∀ provenance,
      let length := eachLen regrow owner sampled le ls
      let compared := Goose.Lower.emitDef (.cmp .lt .i64 counter length.1) le length.2
      let split := fork compared.1 le compared.2
      let started := eachLoopBodyEntry regrow owner sampled counter le ls
      ReplayBuilder module results vt func target le scopeCount slots started provenance →
      OccurrenceSitesBuilder env siteRoot (split.1.2 :: siteTargets) le started func vt provenance →
      ReplacementTargetsBound (split.1.2 :: siteTargets) started →
      GeneratedBuilderState started → NativeRows vt (body compared.2.stack.length split.1.2 le started).2 →
      header < started.blocks.size → split.1.2 < started.blocks.size → counter < started.vals.size → rootsAt provenance.vals counter = [] →
      view < started.vals.size → Goose.GIR.RootsRefine func (rootsAt provenance.vals view) sourceRoots →
      (∃ mu, started.vals[view]? = some (some (.view mu element))) →
      started.vals[counter]? = some (some (.data (.int .i64))) →
      SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func (body compared.2.stack.length split.1.2 le started).2 →
      NativeBuilderContinuation func (body compared.2.stack.length split.1.2 le started).2 →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (body compared.2.stack.length split.1.2 le started).2 next ∧
        (∀ old, old < provenance.vals.size → rootsAt next.vals old = rootsAt provenance.vals old) ∧
        ReturnBoundsPreserved expected started provenance (body compared.2.stack.length split.1.2 le started).2 next ∧
        OccurrenceLedger env root func vt next started (body compared.2.stack.length split.1.2 le started).2 ∧
        OccurrenceSitesBuilder env siteRoot (split.1.2 :: siteTargets) le (body compared.2.stack.length split.1.2 le started).2 func vt next) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots (lowerEach regrow owner sampled header counter body le ls).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved expected ls upper (lowerEach regrow owner sampled header counter body le ls).2 next ∧
      OccurrenceLedger env root func vt next ls (lowerEach regrow owner sampled header counter body le ls).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets le (lowerEach regrow owner sampled header counter body le ls).2 func vt next := by
  let length := eachLen regrow owner sampled le ls
  obtain ⟨lengthProv, lengthReady, lengthValue, lengthGrowth⟩ := ready.loopEachLength regrow owner sampled sourceRoots closed input reads sample
  have lengthAdv := advB_eachLen regrow owner sampled le ls length.1 length.2 rfl
  have lengthGenerated := generated.eachLen regrow owner sampled (rfl : eachLen regrow owner sampled le ls = length)
  have lengthLive : length.2.cur.isSome = true := by
    cases regrow with
    | false => exact live
    | true =>
      cases current : ls.cur with
      | none => simp [current] at live
      | some block => simpa [length, eachLen, emitDef_run _ _ current, current]
  have whole : lowerEach regrow owner sampled header counter body le ls = lowerRange .i64 counter length.1 header body le length.2 := rfl
  have nativeRange : NativeRows vt (lowerRange .i64 counter length.1 header body le length.2).2 := native
  have oldCounter : counter < upper.vals.size := by simpa only [ready.roots.valueSize] using counterBound
  have lengthGhostGrowth := accessRootsGrowth ready lengthReady lengthAdv.vals
  have lengthSites : OccurrenceSitesBuilder env siteRoot siteTargets le length.2 func vt lengthProv := by
    cases regrow with
    | true => exact sites.emitDef rfl lengthGhostGrowth lengthGrowth
    | false => exact sites.ghost_retained lengthGhostGrowth lengthGrowth
  have lengthLedger : OccurrenceLedger env root func vt lengthProv ls length.2 := by
    cases regrow with
    | false => exact .refl _ _
    | true =>
      apply accessEmitDefinition rfl
      intro active
      refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store (by intros; intro same; cases same), ?_⟩
      · intro operand member reference
        have same : operand = owner.getD 0 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
        subst operand
        have bounded : owner.getD 0 < upper.vals.size := by simpa only [ready.roots.valueSize] using (input rfl).1
        apply sourceView.operand (Nat.lt_of_lt_of_le bounded lengthGhostGrowth)
        rw [lengthGrowth _ bounded]
        exact (input rfl).2
      · intro value address same; cases same
      · intro value callee args origin same; cases same
      · intro operand member mutability payload row
        have same : operand = owner.getD 0 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
        subst operand
        obtain ⟨place, shape⟩ := ownerSource rfl
        have bounded : owner.getD 0 < upper.vals.size := by simpa only [ready.roots.valueSize] using (input rfl).1
        apply sourceView.consumedPlace shape (Nat.lt_of_lt_of_le bounded lengthGhostGrowth)
        rw [lengthGrowth _ bounded]
        exact (input rfl).2
  have counterType : valRefLike vt counter = false := by
    have recorded : vt[counter]? = some (some (.data (.int .i64))) :=
      (nativeRange.of_prefix (types_lowerRange .i64 counter length.1 header bodyTypes le length.2 _ _ rfl)) _ _
        ((types_eachLen regrow owner sampled le ls _ _ rfl) _ _ counterRow)
    simp [valRefLike, recorded, VTy.refLike, Ty.isRefLike]
  have lengthNative := nativeRange.of_prefix (types_lowerRange .i64 counter length.1 header bodyTypes le length.2 _ _ rfl)
  have lengthType : valRefLike vt length.1 = false := by
    cases regrow with
    | false => exact sampleType rfl
    | true => exact native_arrayLen_scalar lengthNative rfl live
  obtain ⟨next, nextReady, growth, transfer, rangeLedger, finalSites⟩ := loopRangeOccurrence
    (root := root) lengthReady lengthSites (targetBounds.mono lengthAdv.ext) expected .i64 counter length.1 header body lengthLive
    (Nat.lt_of_lt_of_le headerBound lengthAdv.ext.1) (Nat.lt_of_lt_of_le counterBound lengthAdv.vals)
    (lengthValue lengthLive).bound ((lengthGrowth counter oldCounter).trans counterScalar) counterType lengthType headerIncluded lengthGenerated nativeRange projects continuation bodyAdv
    (by
      intro provenance
      dsimp only
      intro stateReady stateSites stateBounds stateGenerated stateNative headerBound exitBound counterBound counterEmpty priorRoots bodyProjects bodyContinuation
      have entryTypes := native_each_entry_types regrow owner sampled counter le ls
      obtain ⟨mu, row⟩ := viewRow
      have recordedView := entryTypes view (.view mu element) row
      have viewOld : view < upper.vals.size := by simpa only [ready.roots.valueSize] using viewBound
      have viewLength : view < lengthProv.vals.size := by
        rw [lengthReady.roots.valueSize]
        exact Nat.lt_of_lt_of_le viewBound lengthAdv.vals
      apply bodyStep provenance stateReady stateSites stateBounds stateGenerated stateNative headerBound exitBound counterBound counterEmpty
        (Array.getElem?_eq_some_iff.mp recordedView).1
      · rw [priorRoots view viewLength, lengthGrowth view viewOld]
        exact viewRefined
      · exact ⟨mu, recordedView⟩
      · exact entryTypes counter (.data (.int .i64)) counterRow
      · exact bodyProjects
      · exact bodyContinuation)
  have frame : ReturnMembershipFrame ls length.2 :=
    ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_eachLen regrow owner sampled) le ls length.1 length.2 rfl
  have lengthTransfer : ReturnBoundsPreserved expected ls upper length.2 lengthProv :=
    .frame ready.symbols ready.roots.valueSize lengthGrowth frame
  refine ⟨next, nextReady, ?_, lengthTransfer.trans transfer, ?_, finalSites⟩
  · intro old bound
    have lengthBound : old < lengthProv.vals.size := by
      rw [lengthReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) lengthAdv.vals
    rw [growth old lengthBound, lengthGrowth old bound]
  · have nextGrowth := accessRootsGrowth lengthReady nextReady
      (advB_lowerRange .i64 counter length.1 header bodyAdv le length.2 _ _ rfl).vals
    exact (lengthLedger.retained nextGrowth growth).trans rangeLedger

#print axioms loopEachOccurrence

end Goose.Lower.Validation.ReplacementContentFlowSource

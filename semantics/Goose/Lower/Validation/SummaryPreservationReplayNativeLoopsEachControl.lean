import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsRangeControl
import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsEachBody

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem native_each_entry_types (regrow : Bool) (owner : Option ValueId) (sampled counter : ValueId) (le : LEnv) (state : LS) :
    TypePrefix state (eachLoopBodyEntry regrow owner sampled counter le state) := by
  let length := eachLen regrow owner sampled le state
  let compared := Goose.Lower.emitDef (.cmp .lt .i64 counter length.1) le length.2
  let split := fork compared.1 le compared.2
  exact (types_eachLen regrow owner sampled le state length.1 length.2 rfl).trans
    ((types_emitDef (.cmp .lt .i64 counter length.1) le length.2 compared.1 compared.2 rfl).trans
      ((types_fork compared.1 le compared.2 split.1 split.2 rfl).trans (types_setCur (some split.1.1) le split.2 _ _ rfl)))

theorem loopEachNative (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (expected : List RootRef) (regrow : Bool) (owner : Option ValueId) (sampled counter view : ValueId) (header : BlockId)
    (element : Ty) (sourceRoots : List RootRef) (body : Nat → BlockId → B ValueId)
    (live : ls.cur.isSome = true) (headerBound : header < ls.blocks.size)
    (counterBound : counter < ls.vals.size) (counterScalar : rootsAt upper.vals counter = [])
    (closed : ParameterRootsClosed func)
    (input : regrow = true → owner.getD 0 < ls.vals.size ∧ RootsRefine func (rootsAt upper.vals (owner.getD 0)) sourceRoots)
    (reads : regrow = true → ∀ item ∈ func.storageTargets (rootsTargets sourceRoots), item ∈ func.storageTargets target.reads)
    (sample : regrow = false → ReplayValue func upper ls sampled [] (.data (.int .i64)))
    (viewBound : view < ls.vals.size) (viewRefined : RootsRefine func (rootsAt upper.vals view) sourceRoots)
    (viewRow : ∃ mu, ls.vals[view]? = some (some (.view mu element)))
    (counterRow : ls.vals[counter]? = some (some (.data (.int .i64))))
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerEach regrow owner sampled header counter body le ls).2)
    (bodyAdv : ∀ depth exit, AdvB (body depth exit))
    (bodyStep : ∀ provenance,
      let length := eachLen regrow owner sampled le ls
      let compared := Goose.Lower.emitDef (.cmp .lt .i64 counter length.1) le length.2
      let split := fork compared.1 le compared.2
      let started := eachLoopBodyEntry regrow owner sampled counter le ls
      ReplayBuilder module results vt func target le scopeCount slots started provenance →
      GeneratedBuilderState started → NativeRows vt (body compared.2.stack.length split.1.2 le started).2 →
      header < started.blocks.size → split.1.2 < started.blocks.size → counter < started.vals.size → rootsAt provenance.vals counter = [] →
      view < started.vals.size → RootsRefine func (rootsAt provenance.vals view) sourceRoots →
      (∃ mu, started.vals[view]? = some (some (.view mu element))) →
      started.vals[counter]? = some (some (.data (.int .i64))) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (body compared.2.stack.length split.1.2 le started).2 next ∧
        (∀ old, old < provenance.vals.size → rootsAt next.vals old = rootsAt provenance.vals old) ∧
        ReturnBoundsPreserved expected started provenance (body compared.2.stack.length split.1.2 le started).2 next) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots (lowerEach regrow owner sampled header counter body le ls).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved expected ls upper (lowerEach regrow owner sampled header counter body le ls).2 next := by
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
  obtain ⟨next, nextReady, growth, transfer⟩ := lengthReady.loopRangeNative expected .i64 counter length.1 header body lengthLive
    (Nat.lt_of_lt_of_le headerBound lengthAdv.ext.1) (Nat.lt_of_lt_of_le counterBound lengthAdv.vals)
    (lengthValue lengthLive).bound ((lengthGrowth counter oldCounter).trans counterScalar) lengthGenerated nativeRange bodyAdv
    (by
      intro provenance
      dsimp only
      intro stateReady stateGenerated stateNative headerBound exitBound counterBound counterEmpty priorRoots
      have entryTypes := native_each_entry_types regrow owner sampled counter le ls
      obtain ⟨mu, row⟩ := viewRow
      have recordedView := entryTypes view (.view mu element) row
      have viewOld : view < upper.vals.size := by simpa only [ready.roots.valueSize] using viewBound
      have viewLength : view < lengthProv.vals.size := by
        rw [lengthReady.roots.valueSize]
        exact Nat.lt_of_lt_of_le viewBound lengthAdv.vals
      apply bodyStep provenance stateReady stateGenerated stateNative headerBound exitBound counterBound counterEmpty
        (Array.getElem?_eq_some_iff.mp recordedView).1
      · rw [priorRoots view viewLength, lengthGrowth view viewOld]
        exact viewRefined
      · exact ⟨mu, recordedView⟩
      · exact entryTypes counter (.data (.int .i64)) counterRow)
  have frame : ReturnMembershipFrame ls length.2 :=
    ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_eachLen regrow owner sampled) le ls length.1 length.2 rfl
  have lengthTransfer : ReturnBoundsPreserved expected ls upper length.2 lengthProv :=
    .frame ready.symbols ready.roots.valueSize lengthGrowth frame
  refine ⟨next, nextReady, ?_, lengthTransfer.trans transfer⟩
  intro old bound
  have lengthBound : old < lengthProv.vals.size := by
    rw [lengthReady.roots.valueSize]
    exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) lengthAdv.vals
  rw [growth old lengthBound, lengthGrowth old bound]

#print axioms loopEachNative

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

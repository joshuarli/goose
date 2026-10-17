import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsEachControl
import Goose.Lower.Validation.SummaryPreservationReplayTypedViewsEachSource

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

structure NativeEachPrefix where
  sampled : ValueId
  header : BlockId
  counter : ValueId
  state : LS

def nativeEachPrefix (regrow : Bool) (view : ValueId) (le : LEnv) (state : LS) : NativeEachPrefix :=
  let sampled := eachSampled regrow view le state
  let startAt := Goose.Lower.emitDef (.constInt .i64 0) le sampled.2
  let allocated := newBlock [.data (.int .i64)] le startAt.2
  let bridged := Goose.Lower.emitTerm (.br allocated.1.1 [startAt.1]) le allocated.2
  ⟨sampled.1, allocated.1.1, allocated.1.2.headD 0, (Goose.Lower.setCur (some allocated.1.1) le bridged.2).2⟩

def nativeEachPrelude (regrow : Bool) (owner : Option ValueId) (view : ValueId)
    (body : Nat → BlockId → BlockId → ValueId → B ValueId) : B Unit := do
  let sampled ← eachSampled regrow view
  let startAt ← Goose.Lower.emitDef (.constInt .i64 0)
  let (header, parameters) ← newBlock [.data (.int .i64)]
  let counter := parameters.headD 0
  Goose.Lower.emitTerm (.br header [startAt])
  Goose.Lower.setCur (some header)
  lowerEach regrow owner sampled header counter (fun depth exit => body depth header exit counter)

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

set_option maxHeartbeats 1400000

theorem eachPreludeNative (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (expected : List RootRef) (regrow : Bool) (owner : Option ValueId) (view : ValueId) (element : Ty) (sourceRoots : List RootRef)
    (body : Nat → BlockId → BlockId → ValueId → B ValueId)
    (live : ls.cur.isSome = true) (source : ReplayEachSource func upper ls (owner, view) sourceRoots element)
    (closed : ParameterRootsClosed func) (hasOwner : regrow = true → owner.isSome = true)
    (reads : regrow = true → ∀ item ∈ func.storageTargets (rootsTargets sourceRoots), item ∈ func.storageTargets target.reads)
    (viewRow : ∃ mu, ls.vals[view]? = some (some (.view mu element)))
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (nativeEachPrelude regrow owner view body le ls).2)
    (bodyAdv : ∀ depth header exit counter, AdvB (body depth header exit counter))
    (bodyStep : ∀ provenance,
      let prelude := nativeEachPrefix regrow view le ls
      let length := eachLen regrow owner prelude.sampled le prelude.state
      let compared := Goose.Lower.emitDef (.cmp .lt .i64 prelude.counter length.1) le length.2
      let split := fork compared.1 le compared.2
      let entry := eachLoopBodyEntry regrow owner prelude.sampled prelude.counter le prelude.state
      ReplayBuilder module results vt func target le scopeCount slots entry provenance →
      GeneratedBuilderState entry → NativeRows vt (body compared.2.stack.length prelude.header split.1.2 prelude.counter le entry).2 →
      prelude.header < entry.blocks.size → split.1.2 < entry.blocks.size → prelude.counter < entry.vals.size → rootsAt provenance.vals prelude.counter = [] →
      view < entry.vals.size → RootsRefine func (rootsAt provenance.vals view) sourceRoots →
      (∃ mu, entry.vals[view]? = some (some (.view mu element))) → entry.vals[prelude.counter]? = some (some (.data (.int .i64))) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (body compared.2.stack.length prelude.header split.1.2 prelude.counter le entry).2 next ∧
        (∀ old, old < provenance.vals.size → rootsAt next.vals old = rootsAt provenance.vals old) ∧
        ReturnBoundsPreserved expected entry provenance (body compared.2.stack.length prelude.header split.1.2 prelude.counter le entry).2 next) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots (nativeEachPrelude regrow owner view body le ls).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved expected ls upper (nativeEachPrelude regrow owner view body le ls).2 next := by
  let sampled := eachSampled regrow view le ls
  obtain ⟨sampleProv, sampleReady, sampleValue, sampleGrowth⟩ := ready.loopEachSampled regrow view source.view.bound
  have sampleAdv := advB_eachSampled regrow view le ls sampled.1 sampled.2 rfl
  have sampleLive : sampled.2.cur.isSome = true := by
    cases regrow with
    | true => exact live
    | false =>
      cases current : ls.cur with
      | none => simp [current] at live
      | some b => simpa [sampled, eachSampled, emitDef_run _ _ current, current]
  let startAt := Goose.Lower.emitDef (.constInt .i64 0) le sampled.2
  obtain ⟨startProv, startReady, startValue, startGrowth⟩ := sampleReady.emitTypedDef (.constInt .i64 0) [] (.data (.int .i64))
    (by simp [Op.uses]) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
    (effectRefinement_empty func target) (fun _ member => by cases member) (fun _ => rfl)
  have startAdv := advB_emitDef (.constInt .i64 0) le sampled.2 startAt.1 startAt.2 rfl
  obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp sampleLive
  have startCurrent : startAt.2.cur = some block := by simp [startAt, emitDef_run _ _ current, current]
  have startLive : startAt.2.cur.isSome = true := by simp [startCurrent]
  let allocated := newBlock [.data (.int .i64)] le startAt.2
  obtain ⟨headerProv, headerReady, counterScalar, headerGrowth⟩ := startReady.loopScalarBlock (.data (.int .i64))
  let counter := allocated.1.2.headD 0
  have counterEq : counter = startAt.2.vals.size := by simp [counter, allocated, newBlock1_run]
  have headerBound : allocated.1.1 < allocated.2.blocks.size := by simp [allocated, newBlock1_run]
  have counterBound : counter < allocated.2.vals.size := by simp [counterEq, allocated, newBlock1_run]
  have startBound : startAt.1 < startProv.vals.size := by simpa only [startReady.roots.valueSize] using (startValue startLive).bound
  have startEmpty : rootsAt headerProv.vals startAt.1 = [] :=
    (headerGrowth startAt.1 startBound).trans ((startValue startLive).scalar rfl)
  let bridged := Goose.Lower.emitTerm (.br allocated.1.1 [startAt.1]) le allocated.2
  have bridgeReady := headerReady.loopBranch allocated.1.1 [startAt.1] headerBound
    (by simpa [allocated, newBlock1_run] using Nat.lt_succ_of_lt (startValue startLive).bound) (by simpa using startEmpty)
  have bridgeAdv := advB_emitTerm (.br allocated.1.1 [startAt.1]) le allocated.2 bridged.1 bridged.2 rfl
  let started := (Goose.Lower.setCur (some allocated.1.1) le bridged.2).2
  have headerStill := Nat.lt_of_lt_of_le headerBound bridgeAdv.ext.1
  have counterStill := Nat.lt_of_lt_of_le counterBound bridgeAdv.vals
  have startedReady := bridgeReady.setCur (some allocated.1.1) (by intro b row; cases row; exact headerStill)
  have headerAdv := advB_newBlock1 (.data (.int .i64)) le startAt.2 allocated.1 allocated.2 rfl
  have initialGrowth : ∀ i, i < upper.vals.size → rootsAt headerProv.vals i = rootsAt upper.vals i := by
    intro i bound
    have sampleBound : i < sampleProv.vals.size := by
      rw [sampleReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) sampleAdv.vals
    have startBound : i < startProv.vals.size := by
      rw [startReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [sampleReady.roots.valueSize] using sampleBound) startAdv.vals
    rw [headerGrowth i startBound, startGrowth i sampleBound, sampleGrowth i bound]
  have stateGrowth : ls.vals.size ≤ started.vals.size :=
    Nat.le_trans sampleAdv.vals (Nat.le_trans startAdv.vals (Nat.le_trans headerAdv.vals bridgeAdv.vals))
  have ownerInput : regrow = true → owner.getD 0 < started.vals.size ∧ RootsRefine func (rootsAt headerProv.vals (owner.getD 0)) sourceRoots := by
    intro active
    cases owner with
    | none => have impossible := hasOwner active
              cases impossible
    | some address =>
      obtain ⟨bound, refined⟩ := source.owner address rfl
      refine ⟨Nat.lt_of_lt_of_le bound stateGrowth, ?_⟩
      change RootsRefine func (rootsAt headerProv.vals address) sourceRoots
      rw [initialGrowth address (by simpa only [ready.roots.valueSize] using bound)]
      exact refined
  have sampleInput : regrow = false → ReplayValue func headerProv started sampled.1 [] (.data (.int .i64)) := by
    intro inactive
    have value := sampleValue inactive sampleLive
    have sampledBound : sampled.1 < sampleProv.vals.size := by simpa only [sampleReady.roots.valueSize] using value.bound
    have sampleStartBound : sampled.1 < startProv.vals.size := by
      rw [startReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le value.bound startAdv.vals
    have retained : rootsAt headerProv.vals sampled.1 = rootsAt sampleProv.vals sampled.1 :=
      (headerGrowth sampled.1 sampleStartBound).trans (startGrowth sampled.1 sampledBound)
    refine ⟨Nat.lt_of_lt_of_le value.bound (Nat.le_trans startAdv.vals (Nat.le_trans headerAdv.vals bridgeAdv.vals)), ?_, ?_⟩
    · rw [retained]
      exact value.refined
    · intro scalar
      rw [retained]
      exact value.scalar scalar
  have viewOld : view < upper.vals.size := by simpa only [ready.roots.valueSize] using source.view.bound
  have sampleGenerated := generated.eachSampled regrow view (rfl : eachSampled regrow view le ls = sampled)
  have startGenerated := sampleGenerated.emitDef (.constInt .i64 0) (rfl : Goose.Lower.emitDef (.constInt .i64 0) le sampled.2 = startAt)
  have allocatedGenerated := startGenerated.newBlock [.data (.int .i64)]
    (rfl : newBlock [.data (.int .i64)] le startAt.2 = (allocated.1, allocated.2))
  have bridgeGenerated := allocatedGenerated.emitTerm (.br allocated.1.1 [startAt.1])
    (by intro destination member; have same := List.mem_singleton.mp member; subst destination; exact headerBound)
    (rfl : Goose.Lower.emitTerm (.br allocated.1.1 [startAt.1]) le allocated.2 = ((), bridged.2))
  have startedGenerated := bridgeGenerated.setCur (some allocated.1.1) (by intro b row; cases row; exact headerStill)
    (rfl : Goose.Lower.setCur (some allocated.1.1) le bridged.2 = ((), started))
  have whole : nativeEachPrelude regrow owner view body le ls = lowerEach regrow owner sampled.1 allocated.1.1 counter
      (fun depth exit => body depth allocated.1.1 exit counter) le started := by
    simp only [nativeEachPrelude, bind_run]
    rfl
  have startedTypes : TypePrefix ls started :=
    (types_eachSampled regrow view le ls sampled.1 sampled.2 rfl).trans
      ((types_emitDef (.constInt .i64 0) le sampled.2 startAt.1 startAt.2 rfl).trans
        ((types_newBlock [.data (.int .i64)] le startAt.2 allocated.1 allocated.2 rfl).trans
          ((types_emitTerm (.br allocated.1.1 [startAt.1]) le allocated.2 () bridged.2 rfl).trans
            (types_setCur (some allocated.1.1) le bridged.2 () started rfl))))
  obtain ⟨mu, sourceViewRow⟩ := viewRow
  have startedView := startedTypes view (.view mu element) sourceViewRow
  have headerCounter : allocated.2.vals[counter]? = some (some (.data (.int .i64))) := by
    simp [counterEq, allocated, newBlock1_run]
  have startedCounter := ((types_emitTerm (.br allocated.1.1 [startAt.1]) le allocated.2 () bridged.2 rfl).trans
    (types_setCur (some allocated.1.1) le bridged.2 () started rfl)) counter (.data (.int .i64)) headerCounter
  have nativeLoop : NativeRows vt (lowerEach regrow owner sampled.1 allocated.1.1 counter
      (fun depth exit => body depth allocated.1.1 exit counter) le started).2 := by rw [whole] at native; exact native
  obtain ⟨next, nextReady, growth, transfer⟩ := startedReady.loopEachNative expected regrow owner sampled.1 counter view allocated.1.1 element sourceRoots
    (fun depth exit => body depth allocated.1.1 exit counter) (by rfl) headerStill counterStill
    (by simpa only [counterEq] using counterScalar) closed ownerInput reads sampleInput
    (Nat.lt_of_lt_of_le source.view.bound stateGrowth)
    (by rw [initialGrowth view viewOld]; exact source.view.refined) ⟨mu, startedView⟩ startedCounter startedGenerated nativeLoop
    (fun depth exit => bodyAdv depth allocated.1.1 exit counter)
    (by
      intro provenance
      dsimp only
      intro stateReady stateGenerated stateNative headerBound exitBound counterBound counterEmpty viewBound viewRefined actualView actualCounter
      exact bodyStep provenance stateReady stateGenerated stateNative headerBound exitBound counterBound counterEmpty viewBound viewRefined actualView actualCounter)
  have entryReturns : ReturnMembershipFrame ls started := by
    apply ReturnFrameRun.of_absence (fun _ => ReturnFrames.ReturnAbsentRun.bind
      (ReturnFrames.returnAbsent_eachSampled regrow view) (fun _ => ReturnFrames.ReturnAbsentRun.bind
        (ReturnFrames.returnAbsent_emitDef (.constInt .i64 0)) (fun value =>
          ReturnFrames.returnAbsent_header1 (.data (.int .i64)) value (fun _ _ => ReturnFrames.returnAbsent_pure ()))))
      le ls () started
    simp only [bind_run, pure_run]
    rfl
  have entryTransfer : ReturnBoundsPreserved expected ls upper started headerProv :=
    .frame ready.symbols ready.roots.valueSize initialGrowth entryReturns
  refine ⟨next, by rw [whole]; exact nextReady, ?_, ?_⟩
  · intro old bound
    have headerBound : old < headerProv.vals.size := by
      rw [startedReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) stateGrowth
    rw [growth old headerBound, initialGrowth old bound]
  · rw [whole]
    exact entryTransfer.trans transfer

#print axioms eachPreludeNative

end ReplayBuilder
end Goose.Lower.Validation.SummaryPreservation

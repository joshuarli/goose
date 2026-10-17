import Goose.Lower.Validation.SummaryPreservationReplayLoopsEachBody

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem each_sample_cur (regrow : Bool) (view : ValueId) (le : LEnv) (state : LS) :
    (eachSampled regrow view le state).2.cur = state.cur := by
  cases regrow <;> cases current : state.cur <;> simp [eachSampled, emitDef_run, emitDef_none, pure_run, current]

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

set_option maxHeartbeats 1200000

def eachPreludeBodyEntry (regrow : Bool) (owner : Option ValueId) (view : ValueId)
    (le : LEnv) (state : LS) : LS :=
  let sampled := eachSampled regrow view le state
  let startAt := Goose.Lower.emitDef (.constInt .i64 0) le sampled.2
  let allocated := newBlock [.data (.int .i64)] le startAt.2
  let bridged := emitTerm (.br allocated.1.1 [startAt.1]) le allocated.2
  let started := (Goose.Lower.setCur (some allocated.1.1) le bridged.2).2
  eachLoopBodyEntry regrow owner sampled.1 (allocated.1.2.headD 0) le started

theorem eachPrelude (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (regrow : Bool) (owner : Option ValueId) (view : ValueId) (element : Ty) (sourceRoots : List RootRef)
    (body : Nat → BlockId → BlockId → ValueId → B ValueId)
    (live : ls.cur.isSome = true)
    (source : ReplayEachSource func upper ls (owner, view) sourceRoots element)
    (closed : ParameterRootsClosed func)
    (hasOwner : regrow = true → owner.isSome = true)
    (reads : regrow = true → ∀ item ∈ func.storageTargets (rootsTargets sourceRoots), item ∈ func.storageTargets target.reads)
    (bodyAdv : ∀ depth header exit counter, AdvB (body depth header exit counter))
    (bodyStep : ∀ depth header exit counter state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      state = eachPreludeBodyEntry regrow owner view le ls →
      state.cur.isSome = true → header < state.blocks.size → exit < state.blocks.size →
      counter < state.vals.size → rootsAt provenance.vals counter = [] →
      view < state.vals.size → RootsRefine func (rootsAt provenance.vals view) sourceRoots →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots (body depth header exit counter le state).2 next ∧
        ∀ i, i < provenance.vals.size → rootsAt next.vals i = rootsAt provenance.vals i) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
      ((do
        let sampled ← eachSampled regrow view
        let startAt ← Goose.Lower.emitDef (.constInt .i64 0)
        whenLive () fun _ => do
          let (header, parameters) ← newBlock [.data (.int .i64)]
          let counter := parameters.headD 0
          emitTerm (.br header [startAt])
          Goose.Lower.setCur (some header)
          lowerEach regrow owner sampled header counter (fun depth exit => body depth header exit counter)) le ls).2 next ∧
      ∀ i, i < upper.vals.size → rootsAt next.vals i = rootsAt upper.vals i := by
  let sampled := eachSampled regrow view le ls
  obtain ⟨sampleProv, sampleReady, sampleValue, sampleGrowth⟩ := ready.loopEachSampled regrow view source.view.bound
  have sampleAdv := advB_eachSampled regrow view le ls sampled.1 sampled.2 rfl
  have sampleLive : sampled.2.cur.isSome = true := by simpa only [sampled, each_sample_cur] using live
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
  let bridged := emitTerm (.br allocated.1.1 [startAt.1]) le allocated.2
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
  obtain ⟨next, nextReady, growth⟩ := startedReady.loopEach regrow owner sampled.1 counter allocated.1.1 sourceRoots
    (fun depth exit => body depth allocated.1.1 exit counter) (by rfl) headerStill counterStill
    (by simpa only [counterEq] using counterScalar) closed ownerInput reads sampleInput
    (fun d e => bodyAdv d allocated.1.1 e counter)
    (by
      intro depth exit state provenance stateReady stateEq stateLive headerBound exitBound counterBound counterEmpty values priorRoots
      apply bodyStep depth allocated.1.1 exit counter state provenance stateReady stateEq stateLive headerBound exitBound counterBound counterEmpty
        (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le source.view.bound stateGrowth) values)
      have viewHeader : view < headerProv.vals.size := by
        rw [startedReady.roots.valueSize]
        exact Nat.lt_of_lt_of_le source.view.bound stateGrowth
      rw [priorRoots view viewHeader, initialGrowth view viewOld]
      exact source.view.refined)
  refine ⟨next, ?_, ?_⟩
  · simp only [bind_run]
    change ReplayBuilder module results vt func target le scopeCount slots (whenLive () _ le startAt.2).2 next
    rw [whenLive_some _ _ _ startCurrent]
    simpa only [bind_run] using nextReady
  · intro i bound
    have headerBound : i < headerProv.vals.size := by
      rw [startedReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) stateGrowth
    rw [growth i headerBound, initialGrowth i bound]

#print axioms eachPrelude

end ReplayBuilder
end Goose.Lower.Validation.SummaryPreservation

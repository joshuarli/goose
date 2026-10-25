import Goose.Lower.Validation.SourceReadyTypedStatementsEach
import Goose.Lower.Validation.SourceReadyObservationTypedLoopsEachPrepared

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.observedTypedEach {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS}
    {typingEnv output : TEnv} {results : List Ty} {loop : Option LoopCtx}
    {scope start finish : Nat} {origin : OriginId} {slot : VarId} {indexSlot : Option VarId}
    {view : View} {byReference : Bool} {body : Core.Block}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyStmt typingEnv scope (.forEach slot indexSlot view byReference body origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before) (readable : SourceReadableEnvironment typingEnv)
    (slotCount : func.slots.size = typingEnv.vars.size)
    (native : SummaryPreservation.NativeRows types
      (lowerStmt loop (.forEach slot indexSlot view byReference body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.forEach slot indexSlot view byReference body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.forEach slot indexSlot view byReference body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (viewChild : ∀ element writable next last, Core.tyView typingEnv view next = .ok ((element, writable), last) →
      ValueReadyAt state (lowerView view) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (placeChild : ∀ place info next last, view = .of place → Core.tyPlace typingEnv place next = .ok (info, last) →
      ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (bodyChild : ∀ (type : Ty) (next : Nat) (context : LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (initial : LS),
      Core.tyBlock { typingEnv with loops := typingEnv.loops + 1, visible := slot :: indexSlot.toList ++ typingEnv.visible }
        [] body next = .ok (type, finish) →
      GeneratedBuilderState initial →
      LoopBuilderTargets (some context) initial →
      SummaryPreservation.NativeRows types (Lower.lowerBlock (some context) pre false body
        (lowerEnv typingEnv.mod typingEnv.vars results) initial).2 →
      (Lower.lowerBlock (some context) pre false body (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.Ext completed →
      (Lower.lowerBlock (some context) pre false body (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady { typingEnv with loops := typingEnv.loops + 1, visible := slot :: indexSlot.toList ++ typingEnv.visible } state →
      (∀ selected input org, (selected, input, org) ∈ pre → selected < func.slots.size) →
      (∀ selected input org, (selected, input, org) ∈ pre → flowAt state.values input ≠ .pending) →
      (∀ nextHeader nextType nextIndex, context.cont = .next nextHeader nextType nextIndex →
        flowAt state.values nextIndex ≠ .pending) →
      EmitsOnly (ReadyOperands state) initial (Lower.lowerBlock (some context) pre false body
        (lowerEnv typingEnv.mod typingEnv.vars results) initial).2 ∧
      EmitsOnly (ReadyCallObservations module func state) initial (Lower.lowerBlock (some context) pre false body
        (lowerEnv typingEnv.mod typingEnv.vars results) initial).2) :
    (EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.forEach slot indexSlot view byReference body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.forEach slot indexSlot view byReference body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before
        (lowerStmt loop (.forEach slot indexSlot view byReference body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType,
    declared, indexChecked, viewSource, _, bodySource, outputEq⟩ := tyStmt_forEach_children source
  subst output
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let sourced := lowerEachSource view env before
  have sourceEquality : sourced.2 = (lowerView view env before).2 ∧ sourced.1.2 = (lowerView view env before).1 := by
    cases view <;> exact ⟨rfl, rfl⟩
  have viewPair := viewChild element writable viewStart viewFinish viewSource
  have viewed := viewPair.1
  have viewEmits : EmitsOnly (ReadyOperands state) before sourced.2 := sourceEquality.1 ▸ viewed.1
  have viewReady : sourced.2.cur.isSome = true → flowAt state.values sourced.1.2 ≠ .pending := by
    rw [sourceEquality.1, sourceEquality.2]
    exact viewed.2
  have ownerReady : ∀ address, sourced.1.1 = some address → sourced.2.cur.isSome = true → flowAt state.values address ≠ .pending := by
    intro address ownerRow live
    cases shape : view with
    | val expression =>
      simp only [sourced, shape, lowerEachSource, bind_run, pure_run] at ownerRow
      contradiction
    | of place =>
      have checked := viewSource
      rw [shape] at checked
      obtain ⟨info, next, placeSource, _⟩ := (st_bind_ok _ _ _ _).mp checked
      have placePair := placeChild place info viewStart next shape placeSource
      have placeReady := placePair.1
      have same : address = (lowerPlace place env before).1 := by
        simpa only [sourced, shape, lowerEachSource, bind_run, pure_run, Option.some.injEq] using ownerRow.symm
      rw [same]
      exact placeReady.2 (by
        simpa only [sourced, shape, lowerEachSource, bind_run, pure_run, ready_def_current] using live)
  have sourceRow : sourced.2.cur.isSome = true → ∃ mu, sourced.2.vals[sourced.1.2]? = some (some (.view mu element)) := by
    rw [sourceEquality.1, sourceEquality.2]
    intro live
    exact lowerView_generated_typed view viewSource rfl live generated
  have slotBound : slot < func.slots.size := by
    rw [slotCount]
    exact (Array.getElem?_eq_some_iff.mp (declare_ok _ _ _ _ _ declared).2.1).1
  have indexBound : ∀ selected, indexSlot = some selected → selected < func.slots.size := by
    intro selected row
    obtain ⟨_, indexVar, variableRow, _, _⟩ := (declareIndex_ok _ _ _ _ _ indexChecked).2 selected row
    rw [slotCount]
    exact (Array.getElem?_eq_some_iff.mp variableRow).1
  have sourcedGenerated : GeneratedBuilderState sourced.2 := generated.lowerEachSource view rfl
  let bodyAction := fun header index depth exit => do
    let address ← Lower.emitDef (.refElem sourced.1.2 index)
    let value ← Lower.eachElemValue slot byReference address
    Lower.lowerBlock (some ⟨depth, exit, .next header .i64 index⟩)
      ((slot, value, origin) :: indexSlot.toList.map (fun s => (s, index, origin))) false body
  let action : B Unit := do
    let regrow ← regrowOf sourced.1.1
    let sampled ← eachSampled regrow sourced.1.2
    let initial ← Lower.emitDef (.constInt .i64 0)
    whenLive () fun _ => do
      let (header, parameters) ← newBlock [.data (.int .i64)]
      let index := parameters.headD 0
      emitTerm (.br header [initial])
      setCur (some header)
      Lower.lowerEach regrow sourced.1.1 sampled header index (bodyAction header index)
  have actual : (action env sourced.2).2 =
      (lowerStmt loop (.forEach slot indexSlot view byReference body origin) env before).2 := by
    cases indexSlot <;> rfl
  have actionExtension : (action env sourced.2).2.Ext completed := by rw [actual]; exact extension
  have actionAllocated : (action env sourced.2).2.vals.size ≤ completed.vals.size := by rw [actual]; exact allocated
  have actionNative : SummaryPreservation.NativeRows types (action env sourced.2).2 := by rw [actual]; exact native
  have prepared :=
    frame.observedEachPrepared (before := sourced.2) (view := sourced.1.2) (owner := sourced.1.1)
      (byReference := byReference) (origin := origin) bodySource sourcedGenerated visible
      (source_view_element_flat view readable viewSource) sourceRow viewReady ownerReady slotBound indexBound
      (bodyChild bodyType viewFinish) actionExtension actionAllocated actionNative
  have viewObserved : EmitsOnly (ReadyCallObservations module func state) before sourced.2 :=
    sourceEquality.1 ▸ viewPair.2
  refine ⟨⟨?_, fun _ => visible⟩, ?_⟩
  · rw [← actual]
    exact viewEmits.trans prepared.1
  · rw [← actual]
    exact viewObserved.trans prepared.2

end Goose.Lower.Validation.ReplacementContentFlowSource

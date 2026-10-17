import Goose.Lower.Validation.SourceReadyTypedStatementsEachFrames
import Goose.Lower.Validation.SourceReadyObservationTypedLoopsEach

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.observedTypedEachFrames {module : GIR.Module} {callees : Array State} {func : Func}
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
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state → ValueReadyAt state (lowerView view) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerView view (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (placeChild : ∀ place info next last, view = .of place → Core.tyPlace typingEnv place next = .ok (info, last) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state → ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
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
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let sourced := lowerEachSource view env before
  let bodyAction := fun header index depth exit => do
    let address ← Lower.emitDef (.refElem sourced.1.2 index)
    let value ← Lower.eachElemValue slot byReference address
    Lower.lowerBlock (some ⟨depth, exit, .next header .i64 index⟩)
      ((slot, value, origin) :: indexSlot.toList.map (fun s => (s, index, origin))) false body
  let tail : B Unit := do
    let regrow ← regrowOf sourced.1.1
    let sampled ← eachSampled regrow sourced.1.2
    let initial ← Lower.emitDef (.constInt .i64 0)
    whenLive () fun _ => do
      let (header, parameters) ← newBlock [.data (.int .i64)]
      let index := parameters.headD 0
      emitTerm (.br header [initial])
      setCur (some header)
      Lower.lowerEach regrow sourced.1.1 sampled header index (bodyAction header index)
  have bodyAdvance : ∀ header index depth exit, AdvB (bodyAction header index depth exit) := by
    intro header index depth exit
    exact AdvB.bind (advB_emitDef _) fun address => AdvB.bind (advB_eachElemValue _ _ _) fun value =>
      advB_lowerBlock _ _ _ body
  have bodyTypes : ∀ header index depth exit, TypeRun (bodyAction header index depth exit) := by
    intro header index depth exit
    exact TypeRun.bind (types_emitDef _) fun address => TypeRun.bind (types_eachElemValue _ _ _) fun value =>
      types_lowerBlock _ _ _ body
  have tailAdvance : AdvB tail := by
    refine AdvB.bind (advB_regrowOf _) fun regrow => AdvB.bind (advB_eachSampled _ _) fun sampled =>
      AdvB.bind (advB_emitDef _) fun initial => advB_whenLive _ fun _ => ?_
    exact advB_header1 (.data (.int .i64)) initial
      (tail := fun header index => Lower.lowerEach regrow sourced.1.1 sampled header index (bodyAction header index))
      (fun header index => advB_lowerEach regrow sourced.1.1 sampled header index (bodyAdvance header index))
  have tailTypes : TypeRun tail := by
    refine TypeRun.bind (types_regrowOf _) fun regrow => TypeRun.bind (types_eachSampled _ _) fun sampled =>
      TypeRun.bind (types_emitDef _) fun initial => types_whenLive _ fun _ => ?_
    exact types_header1 (.data (.int .i64)) initial
      (tail := fun header index => Lower.lowerEach regrow sourced.1.1 sampled header index (bodyAction header index))
      (fun header index => types_lowerEach regrow sourced.1.1 sampled header index (bodyTypes header index))
  have actual : (tail env sourced.2).2 = (lowerStmt loop (.forEach slot indexSlot view byReference body origin) env before).2 := by
    cases indexSlot <;> rfl
  have sourceExtension : sourced.2.Ext completed := (tailAdvance env sourced.2 _ _ rfl).ext.trans (actual.symm ▸ extension)
  have sourceCount : sourced.2.vals.size ≤ completed.vals.size := Nat.le_trans (tailAdvance env sourced.2 _ _ rfl).vals (actual.symm ▸ allocated)
  have sourceNative : SummaryPreservation.NativeRows types sourced.2 :=
    (show SummaryPreservation.NativeRows types (tail env sourced.2).2 from actual.symm ▸ native).of_prefix
      (tailTypes env sourced.2 _ _ rfl)
  have sourceEquality : sourced.2 = (lowerView view env before).2 := by cases view <;> rfl
  have viewExtension : (lowerView view env before).2.Ext completed := sourceEquality ▸ sourceExtension
  have viewCount : (lowerView view env before).2.vals.size ≤ completed.vals.size := sourceEquality ▸ sourceCount
  have viewNative : SummaryPreservation.NativeRows types (lowerView view env before).2 := sourceEquality ▸ sourceNative
  refine frame.observedTypedEach source generated readable slotCount native extension allocated visible
    (fun element writable next last checked => viewChild element writable next last checked generated viewNative viewExtension viewCount visible) ?_ bodyChild
  intro place info next last shape checked
  let address := lowerPlace place env before
  let mode := match place with | .var _ | .global _ => SnapshotMode.owner | _ => SnapshotMode.borrowed
  have snapshotAdvance : address.2.Adv (lowerView (.of place) env before).2 :=
    advB_emitDef (.snapshot mode address.1) env address.2 _ _ rfl
  have snapshotTypes : TypePrefix address.2 (lowerView (.of place) env before).2 :=
    types_emitDef (.snapshot mode address.1) env address.2 _ _ rfl
  have actualViewNative : SummaryPreservation.NativeRows types (lowerView (.of place) env before).2 := by
    have h := viewNative; rw [shape] at h; exact h
  have actualViewExtension : (lowerView (.of place) env before).2.Ext completed := by
    have h := viewExtension; rw [shape] at h; exact h
  have actualViewCount : (lowerView (.of place) env before).2.vals.size ≤ completed.vals.size := by
    have h := viewCount; rw [shape] at h; exact h
  exact placeChild place info next last shape checked generated (actualViewNative.of_prefix snapshotTypes)
    (snapshotAdvance.ext.trans actualViewExtension) (Nat.le_trans snapshotAdvance.vals actualViewCount) visible

end Goose.Lower.Validation.ReplacementContentFlowSource

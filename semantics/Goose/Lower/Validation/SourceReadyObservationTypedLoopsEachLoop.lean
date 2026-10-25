import Goose.Lower.Validation.SourceReadyTypedStatementsEachLoop
import Goose.Lower.Validation.SourceReadyObservationTypedLoopsEachBody

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.observedEachLoop {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS}
    {typingEnv : TEnv} {results : List Ty} {slot : VarId} {indexSlot : Option VarId}
    {view index sampled : ValueId} {owner : Option ValueId} {regrow byReference : Bool}
    {element : Ty} {mu : Mutability} {header : BlockId}
    {origin : OriginId} {body : Core.Block} {bodyType : Ty} {start finish : Nat}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyBlock { typingEnv with loops := typingEnv.loops + 1, visible := slot :: indexSlot.toList ++ typingEnv.visible }
      [] body start = .ok (bodyType, finish))
    (generated : GeneratedBuilderState before) (headerBound : header < before.blocks.size) (live : before.cur.isSome = true)
    (visible : VisibleSlotsReady typingEnv state) (flat : element.flat = true)
    (viewRow : before.vals[view]? = some (some (.view mu element)))
    (indexRow : before.vals[index]? = some (some (.data (.int .i64))))
    (viewReady : flowAt state.values view ≠ .pending) (indexReady : flowAt state.values index ≠ .pending)
    (ownerReady : regrow = true → flowAt state.values (owner.getD 0) ≠ .pending)
    (sampleReady : regrow = false → flowAt state.values sampled ≠ .pending)
    (slotBound : slot < func.slots.size)
    (indexBound : ∀ selected, indexSlot = some selected → selected < func.slots.size)
    (child : ∀ (context : LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (initial : LS),
      Core.tyBlock { typingEnv with loops := typingEnv.loops + 1, visible := slot :: indexSlot.toList ++ typingEnv.visible }
        [] body start = .ok (bodyType, finish) →
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
    let env := lowerEnv typingEnv.mod typingEnv.vars results
    let bodyAction := fun depth exit => do
      let address ← Lower.emitDef (.refElem view index)
      let value ← Lower.eachElemValue slot byReference address
      Lower.lowerBlock (some ⟨depth, exit, .next header .i64 index⟩)
        ((slot, value, origin) :: indexSlot.toList.map (fun s => (s, index, origin))) false body
    (Lower.lowerEach regrow owner sampled header index bodyAction env before).2.Ext completed →
    (Lower.lowerEach regrow owner sampled header index bodyAction env before).2.vals.size ≤ completed.vals.size →
    SummaryPreservation.NativeRows types (Lower.lowerEach regrow owner sampled header index bodyAction env before).2 →
    EmitsOnly (ReadyOperands state) before (Lower.lowerEach regrow owner sampled header index bodyAction env before).2 ∧
    EmitsOnly (ReadyCallObservations module func state) before (Lower.lowerEach regrow owner sampled header index bodyAction env before).2 := by
  intro env bodyAction extension allocated native
  let iterated := Lower.lowerEach regrow owner sampled header index bodyAction env before
  have bodyAdvance : ∀ depth exit, AdvB (bodyAction depth exit) := by
    intro depth exit
    apply AdvB.bind (advB_emitDef _)
    intro address
    apply AdvB.bind (advB_eachElemValue _ _ _)
    intro value
    exact advB_lowerBlock _ _ _ _
  let length := Lower.eachLen regrow owner sampled env before
  let compared := Lower.emitDef (.cmp .lt .i64 index length.1) env length.2
  let forked := fork compared.1 env compared.2
  let selected := { forked.2 with cur := some forked.1.1 }
  let finished := bodyAction compared.2.stack.length forked.1.2 env selected
  let returned := (Lower.rangeBack .i64 index header env finished.2).2
  have finalState : iterated.2 = { returned with cur := some forked.1.2 } :=
    ready_each_state regrow owner sampled header index bodyAction env before
  have returnedExtension : returned.Ext completed := by
    have actual : iterated.2.Ext completed := extension
    rw [finalState] at actual
    exact actual
  have returnedAllocated : returned.vals.size ≤ completed.vals.size := by
    have actual : iterated.2.vals.size ≤ completed.vals.size := allocated
    rw [finalState] at actual
    exact actual
  have returnedNative : SummaryPreservation.NativeRows types returned := by
    have actual : SummaryPreservation.NativeRows types iterated.2 := native
    rw [finalState] at actual
    exact actual
  have backAdvance : finished.2.Adv returned := advB_rangeBack .i64 index header env finished.2 _ _ rfl
  have finishedExtension : finished.2.Ext completed := backAdvance.ext.trans returnedExtension
  have finishedAllocated : finished.2.vals.size ≤ completed.vals.size := Nat.le_trans backAdvance.vals returnedAllocated
  have finishedNative : SummaryPreservation.NativeRows types finished.2 := returnedNative.of_prefix
    (types_rangeBack .i64 index header env finished.2 _ _ rfl)
  have lengthGenerated : GeneratedBuilderState length.2 := generated.eachLen (env := env) _ _ _ rfl
  have comparedGenerated : GeneratedBuilderState compared.2 := lengthGenerated.emitDef (env := env) _ rfl
  have forkedGenerated : GeneratedBuilderState forked.2 := comparedGenerated.fork (env := env) compared.1 rfl
  have forkIds : forked.1 = (compared.2.blocks.size, compared.2.blocks.size + 1) ∧
      forked.2.blocks.size = compared.2.blocks.size + 2 := fork_ids rfl
  have selectedGenerated : GeneratedBuilderState selected := forkedGenerated.setCur (env := env) _ (by
    intro selectedBlock same
    have equal := Option.some.inj same
    subst selectedBlock
    have id := congrArg Prod.fst forkIds.1
    have size := forkIds.2
    nat_omega) rfl
  have toSelected : TypePrefix before selected :=
    (types_eachLen regrow owner sampled env before _ _ rfl).trans
      ((types_emitDef (.cmp .lt .i64 index length.1) env length.2 _ _ rfl).trans
        ((types_fork compared.1 env compared.2 _ _ rfl).trans
          (types_setCur (some forked.1.1) env forked.2 _ _ rfl)))
  have actualView := toSelected view (.view mu element) viewRow
  have actualIndex := toSelected index (.data (.int .i64)) indexRow
  have growth : before.blocks.size ≤ selected.blocks.size :=
    Nat.le_trans (advB_eachLen regrow owner sampled env before _ _ rfl).ext.1
      (Nat.le_trans (advB_emitDef (.cmp .lt .i64 index length.1) env length.2 _ _ rfl).ext.1
        (advB_fork compared.1 env compared.2 _ _ rfl).ext.1)
  have bodyTargets : LoopBuilderTargets (some ⟨compared.2.stack.length, forked.1.2, .next header .i64 index⟩) selected := by
    constructor
    · have id := congrArg Prod.snd forkIds.1
      have size := forkIds.2
      change forked.1.2 < forked.2.blocks.size
      nat_omega
    · exact Nat.lt_of_lt_of_le headerBound growth
  have continuation : ∀ nextHeader nextType nextIndex,
      (ContKind.next header .i64 index) = .next nextHeader nextType nextIndex →
      flowAt state.values nextIndex ≠ .pending := by
    intro nextHeader nextType nextIndex same
    cases same
    exact indexReady
  have bodyPair := frame.observedTypedEachBody source visible flat actualView actualIndex slotBound indexBound selectedGenerated bodyTargets continuation rfl
    viewReady indexReady finishedExtension finishedAllocated finishedNative
    (by
      intro envChild addressChild valueChild preChild bodySource bodyGenerated bodyTargets bodyNative bodyExtension bodyAllocated bodyVisible preBounds preReady counter
      exact child _ _ _ bodySource bodyGenerated bodyTargets bodyNative bodyExtension bodyAllocated bodyVisible preBounds preReady counter)
  exact ⟨frame.lowerEach extension allocated generated.live live indexReady ownerReady sampleReady bodyAdvance bodyPair.1,
    observation_each regrow owner sampled header index bodyAction bodyPair.2⟩

end Goose.Lower.Validation.ReplacementContentFlowSource

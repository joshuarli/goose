import Goose.Lower.Validation.SourceReadyTypedStatementsEachBody
import Goose.Lower.Validation.SourceReadyObservationLoopsEach

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.observedTypedEachBody {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS}
    {typingEnv : TEnv} {results : List Ty} {context : LoopCtx}
    {slot : VarId} {indexSlot : Option VarId} {view index : ValueId} {byReference : Bool}
    {element : Ty} {mu : Mutability} {origin : OriginId} {body : Core.Block} {bodyType : Ty} {start finish : Nat}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyBlock { typingEnv with
        loops := typingEnv.loops + 1
        visible := slot :: indexSlot.toList ++ typingEnv.visible } [] body start = .ok (bodyType, finish))
    (visible : VisibleSlotsReady typingEnv state)
    (flat : element.flat = true)
    (viewRow : before.vals[view]? = some (some (.view mu element)))
    (indexRow : before.vals[index]? = some (some (.data (.int .i64))))
    (slotBound : slot < func.slots.size)
    (indexBound : ∀ selected, indexSlot = some selected → selected < func.slots.size)
    (generated : GeneratedBuilderState before)
    (targets : LoopBuilderTargets (some context) before)
    (counter : ∀ nextHeader nextType nextIndex, context.cont = .next nextHeader nextType nextIndex →
      flowAt state.values nextIndex ≠ .pending)
    (live : before.cur.isSome = true)
    (viewReady : flowAt state.values view ≠ .pending) (indexReady : flowAt state.values index ≠ .pending)
    (extension : ((do
      let address ← Lower.emitDef (.refElem view index)
      let value ← Lower.eachElemValue slot byReference address
      Lower.lowerBlock (some context) ((slot, value, origin) :: indexSlot.toList.map (fun s => (s, index, origin))) false body
      : B ValueId) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : ((do
      let address ← Lower.emitDef (.refElem view index)
      let value ← Lower.eachElemValue slot byReference address
      Lower.lowerBlock (some context) ((slot, value, origin) :: indexSlot.toList.map (fun s => (s, index, origin))) false body
      : B ValueId) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (native : SummaryPreservation.NativeRows types ((do
      let address ← Lower.emitDef (.refElem view index)
      let value ← Lower.eachElemValue slot byReference address
      Lower.lowerBlock (some context) ((slot, value, origin) :: indexSlot.toList.map (fun s => (s, index, origin))) false body
      : B ValueId) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (child :
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let address := Lower.emitDef (.refElem view index) env before
      let value := Lower.eachElemValue slot byReference address.1 env address.2
      let pre := (slot, value.1, origin) :: indexSlot.toList.map (fun s => (s, index, origin))
      Core.tyBlock { typingEnv with
        loops := typingEnv.loops + 1
        visible := slot :: indexSlot.toList ++ typingEnv.visible } [] body start = .ok (bodyType, finish) →
      GeneratedBuilderState value.2 →
      LoopBuilderTargets (some context) value.2 →
      SummaryPreservation.NativeRows types (Lower.lowerBlock (some context) pre false body env value.2).2 →
      (Lower.lowerBlock (some context) pre false body env value.2).2.Ext completed →
      (Lower.lowerBlock (some context) pre false body env value.2).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady { typingEnv with
        loops := typingEnv.loops + 1
        visible := slot :: indexSlot.toList ++ typingEnv.visible } state →
      (∀ selected input org, (selected, input, org) ∈ pre → selected < func.slots.size) →
      (∀ selected input org, (selected, input, org) ∈ pre → flowAt state.values input ≠ .pending) →
      (∀ nextHeader nextType nextIndex, context.cont = .next nextHeader nextType nextIndex →
        flowAt state.values nextIndex ≠ .pending) →
      EmitsOnly (ReadyOperands state) value.2 (Lower.lowerBlock (some context) pre false body env value.2).2 ∧
      EmitsOnly (ReadyCallObservations module func state) value.2 (Lower.lowerBlock (some context) pre false body env value.2).2) :
    EmitsOnly (ReadyOperands state) before ((do
      let address ← Lower.emitDef (.refElem view index)
      let value ← Lower.eachElemValue slot byReference address
      Lower.lowerBlock (some context) ((slot, value, origin) :: indexSlot.toList.map (fun s => (s, index, origin))) false body
      : B ValueId) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
    EmitsOnly (ReadyCallObservations module func state) before ((do
      let address ← Lower.emitDef (.refElem view index)
      let value ← Lower.eachElemValue slot byReference address
      Lower.lowerBlock (some context) ((slot, value, origin) :: indexSlot.toList.map (fun s => (s, index, origin))) false body
      : B ValueId) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  have bounded := generated.live
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := Lower.emitDef (.refElem view index) env before
  let value := Lower.eachElemValue slot byReference address.1 env address.2
  let pre := (slot, value.1, origin) :: indexSlot.toList.map (fun s => (s, index, origin))
  let finished := Lower.lowerBlock (some context) pre false body env value.2
  have valueAdvance : address.2.Adv value.2 := advB_eachElemValue slot byReference address.1 env address.2 _ _ rfl
  have blockAdvance : value.2.Adv finished.2 := advB_lowerBlock (some context) pre false body env value.2 _ _ rfl
  have valueExtension : value.2.Ext completed := blockAdvance.ext.trans extension
  have valueAllocated : value.2.vals.size ≤ completed.vals.size := Nat.le_trans blockAdvance.vals allocated
  have addressReady := frame.emitDef (show Lower.emitDef (.refElem view index) env before = address from rfl)
    (valueAdvance.ext.trans valueExtension) (Nat.le_trans valueAdvance.vals valueAllocated) bounded (by
      intro _ operand member
      rcases (show operand = view ∨ operand = index from by simpa [Op.uses] using member) with same | same
      · subst operand; exact viewReady
      · subst operand; exact indexReady)
    (by intro _ selected impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
  obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
  have referenceType : (Op.refElem view index).resultTy (tyEnv env before) = .ok (.data (.ref mu element)) := by
    simp [Op.resultTy, TyEnv.viewTy, TyEnv.valTy, TyEnv.intTy, TyEnv.dataTy, tyEnv, viewRow, indexRow,
      pure, Except.pure, bind, Except.bind]
  have addressType : address.2.vals[address.1]? = some (some (.data (.ref mu element))) :=
    (emitDef_recorded current referenceType).2.2.1
  have addressLive : address.2.cur.isSome = true := by rw [ready_def_current]; exact live
  have valueNative : SummaryPreservation.NativeRows types value.2 :=
    native.of_prefix (types_lowerBlock (some context) pre false body env value.2 _ _ rfl)
  have valueReady := frame.eachElemValue valueExtension valueAllocated
    (liveBound_of_advB (advB_emitDef (.refElem view index)) env before bounded) valueNative flat
    (fun _ => ⟨mu, addressType⟩) addressReady.2
  have valueLive : value.2.cur.isSome = true := by rw [ready_eachElem_current]; exact addressLive
  have preBounds : ∀ selected input org, (selected, input, org) ∈ pre → selected < func.slots.size := by
    intro selected input org member
    rcases List.mem_cons.mp member with same | later
    · have equal : selected = slot := congrArg Prod.fst same
      exact equal ▸ slotBound
    · obtain ⟨s, selectedMember, equal⟩ := List.mem_map.mp later
      have same : selected = s := congrArg Prod.fst equal.symm
      subst selected
      exact indexBound s (by simpa using selectedMember)
  have preReady : ∀ selected input org, (selected, input, org) ∈ pre → flowAt state.values input ≠ .pending := by
      intro selected input org member
      rcases List.mem_cons.mp member with same | later
      · have equal : input = value.1 := congrArg (fun p => p.2.1) same
        subst input
        exact valueReady.2 valueLive
      · obtain ⟨s, _, equal⟩ := List.mem_map.mp later
        have same : input = index := congrArg (fun p => p.2.1) equal.symm
        subst input
        exact indexReady
  have initialized := frame.blockPreSlots (before := value.2) (pre := pre) (env := env) extension
    (liveBound_of_adv valueAdvance (liveBound_of_advB (advB_emitDef (.refElem view index)) env before bounded))
    valueLive preBounds preReady
  have bodyVisible : VisibleSlotsReady { typingEnv with
      loops := typingEnv.loops + 1
      visible := slot :: indexSlot.toList ++ typingEnv.visible } state := by
    intro selected member localVar row reference
    rcases List.mem_cons.mp member with same | remaining
    · subst selected
      exact initialized slot value.1 origin (by simp [pre])
    · rcases List.mem_append.mp remaining with indexMember | previous
      · exact initialized selected index origin (by
          apply List.mem_cons_of_mem
          apply List.mem_map.mpr
          exact ⟨selected, indexMember, rfl⟩)
      · exact visible selected previous localVar row reference
  have valueGenerated : GeneratedBuilderState value.2 :=
    (generated.emitDef (.refElem view index) rfl).eachElemValue slot byReference address.1 rfl
  have bodyPair := child source valueGenerated
    (targets.mono (Nat.le_trans (advB_emitDef (.refElem view index) env before _ _ rfl).ext.1 valueAdvance.ext.1))
    native extension allocated bodyVisible preBounds preReady counter
  have addressObserved := ReadyCallObservations.emitDefinition (module := module) (func := func) (state := state) (.refElem view index)
    (by intros; intro same; cases same) env before _ _ rfl
  have valueObserved := observation_eachElement (module := module) (func := func) (state := state) slot byReference address.1 env address.2 _ _ rfl
  exact ⟨addressReady.1.trans (valueReady.1.trans bodyPair.1),
    addressObserved.trans (valueObserved.trans bodyPair.2)⟩

end Goose.Lower.Validation.ReplacementContentFlowSource

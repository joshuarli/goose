import Goose.Lower.Validation.SourceReadyTypedStatementsEachLoop

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem ready_regrow_state (owner : Option ValueId) (env : LEnv) (before : LS) :
    (regrowOf owner env before).2 = before := by
  cases owner with
  | none => rfl
  | some address =>
    simp only [regrowOf, growOwner, bind_run, valTy_run]
    cases (valTy address env before).1 with
    | view _ _ => rfl
    | data type => cases type <;> rfl

theorem SourceReadyFrame.eachPrepared {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS}
    {typingEnv : TEnv} {results : List Ty} {slot : VarId} {indexSlot : Option VarId}
    {view : ValueId} {owner : Option ValueId} {byReference : Bool} {element : Ty}
    {origin : OriginId} {body : Core.Block} {bodyType : Ty} {start finish : Nat}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyBlock { typingEnv with loops := typingEnv.loops + 1, visible := slot :: indexSlot.toList ++ typingEnv.visible }
      [] body start = .ok (bodyType, finish))
    (generated : GeneratedBuilderState before)
    (visible : VisibleSlotsReady typingEnv state) (flat : element.flat = true)
    (viewRow : before.cur.isSome = true → ∃ mu, before.vals[view]? = some (some (.view mu element)))
    (viewReady : before.cur.isSome = true → flowAt state.values view ≠ .pending)
    (ownerReady : ∀ address, owner = some address → before.cur.isSome = true → flowAt state.values address ≠ .pending)
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
        (lowerEnv typingEnv.mod typingEnv.vars results) initial).2) :
    let env := lowerEnv typingEnv.mod typingEnv.vars results
    let bodyAction := fun header index depth exit => do
      let address ← Lower.emitDef (.refElem view index)
      let value ← Lower.eachElemValue slot byReference address
      Lower.lowerBlock (some ⟨depth, exit, .next header .i64 index⟩)
        ((slot, value, origin) :: indexSlot.toList.map (fun s => (s, index, origin))) false body
    let action : B Unit := do
      let regrow ← regrowOf owner
      let sampled ← eachSampled regrow view
      let zero ← Lower.emitDef (.constInt .i64 0)
      whenLive () fun _ => do
        let (header, parameters) ← newBlock [.data (.int .i64)]
        let index := parameters.headD 0
        emitTerm (.br header [zero])
        setCur (some header)
        Lower.lowerEach regrow owner sampled header index (bodyAction header index)
    (action env before).2.Ext completed →
    (action env before).2.vals.size ≤ completed.vals.size →
    SummaryPreservation.NativeRows types (action env before).2 →
    EmitsOnly (ReadyOperands state) before (action env before).2 := by
  intro env bodyAction action extension allocated native
  let regrown := regrowOf owner env before
  let sampled := eachSampled regrown.1 view env regrown.2
  let zeroed := Lower.emitDef (.constInt .i64 0) env sampled.2
  let tail : B Unit := whenLive () fun _ => do
    let (header, parameters) ← newBlock [.data (.int .i64)]
    let index := parameters.headD 0
    emitTerm (.br header [zeroed.1])
    setCur (some header)
    Lower.lowerEach regrown.1 owner sampled.1 header index (bodyAction header index)
  have bodyAdvance : ∀ header index depth exit, AdvB (bodyAction header index depth exit) := by
    intro header index depth exit
    apply AdvB.bind (advB_emitDef _)
    intro address
    apply AdvB.bind (advB_eachElemValue _ _ _)
    intro value
    exact advB_lowerBlock _ _ _ _
  have tailAdvance : zeroed.2.Adv (tail env zeroed.2).2 := by
    apply advB_whenLive () (fun _ => advB_header1 (.data (.int .i64)) zeroed.1 (fun header index =>
      advB_lowerEach regrown.1 owner sampled.1 header index (bodyAdvance header index))) env zeroed.2 _ _ rfl
  have zeroExtension : zeroed.2.Ext completed := tailAdvance.ext.trans extension
  have zeroAllocated : zeroed.2.vals.size ≤ completed.vals.size := Nat.le_trans tailAdvance.vals allocated
  have zeroAdvance : sampled.2.Adv zeroed.2 := adv_emitDef rfl
  have regrownGenerated : GeneratedBuilderState regrown.2 := generated.regrowOf owner rfl
  have sampledGenerated : GeneratedBuilderState sampled.2 := regrownGenerated.eachSampled (env := env) regrown.1 view rfl
  have sampleReady : EmitsOnly (ReadyOperands state) regrown.2 sampled.2 ∧
      (regrown.1 = false → sampled.2.cur.isSome = true → flowAt state.values sampled.1 ≠ .pending) := by
    cases selected : regrown.1 with
    | true =>
      simp only [sampled, selected, eachSampled, reduceIte, pure_run]
      exact ⟨.refl _ _, by simp⟩
    | false =>
      have result := frame.emitDef (show Lower.emitDef (.viewLen view) env regrown.2 = sampled from by
          simp only [sampled, selected, eachSampled, Bool.false_eq_true, reduceIte])
        (zeroAdvance.ext.trans zeroExtension) (Nat.le_trans zeroAdvance.vals zeroAllocated)
        regrownGenerated.live (by
          intro active operand member
          have same : operand = view := by simpa [Op.uses] using member
          subst operand
          exact viewReady ((dead_regrowOf owner).live_before rfl active))
        (by intro _ address impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
      exact ⟨result.1, fun _ => result.2⟩
  have zeroReady := frame.emitDef (show Lower.emitDef (.constInt .i64 0) env sampled.2 = zeroed from rfl)
    zeroExtension zeroAllocated sampledGenerated.live (by intro _ operand member; simp [Op.uses] at member)
    (by intro _ address impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
  have regrowEmits : EmitsOnly (ReadyOperands state) before regrown.2 := .of_blocks (congrArg LS.blocks (ready_regrow_state owner env before))
  have prefixReady := regrowEmits.trans (sampleReady.1.trans zeroReady.1)
  cases current : zeroed.2.cur with
  | none =>
    simp only [action, bind_run]
    rw [whenLive_none _ _ _ current]
    exact prefixReady
  | some block =>
    have live : zeroed.2.cur.isSome = true := by simp [current]
    have sampleLive := (dead_emitDef (.constInt .i64 0)).live_before (show Lower.emitDef _ env sampled.2 = zeroed from rfl) live
    have regrownLive := (dead_eachSampled regrown.1 view).live_before (show eachSampled _ _ env regrown.2 = sampled from rfl) sampleLive
    have beforeLive := (dead_regrowOf owner).live_before (show regrowOf owner env before = regrown from rfl) regrownLive
    let created := newBlock [.data (.int .i64)] env zeroed.2
    let index := created.1.2.headD 0
    let closed := (emitTerm (.br created.1.1 [zeroed.1]) env created.2).2
    let started := { closed with cur := some created.1.1 }
    let iterated := Lower.lowerEach regrown.1 owner sampled.1 created.1.1 index (bodyAction created.1.1 index) env started
    have actual : (action env before).2 = iterated.2 := by
      simp only [action, bind_run]
      rw [whenLive_some _ _ _ current]
      rfl
    have iterExtension : iterated.2.Ext completed := actual ▸ extension
    have iterAllocated : iterated.2.vals.size ≤ completed.vals.size := actual ▸ allocated
    have iterNative : SummaryPreservation.NativeRows types iterated.2 := actual ▸ native
    have iterAdvance : started.Adv iterated.2 := advB_lowerEach _ _ _ _ _ (bodyAdvance _ _) env started _ _ rfl
    have closedExtension : closed.Ext completed :=
      ((EmitsOnly.of_blocks (property := ReadyOperands state) rfl).extension : closed.Ext started).trans
        (iterAdvance.ext.trans iterExtension)
    have createdCurrent : created.2.cur = some block := current
    have indexAllocated : zeroed.2.vals.size < completed.vals.size := by
      have count := Nat.le_trans iterAdvance.vals iterAllocated
      have size : started.vals.size = zeroed.2.vals.size + 1 := by
        change (emitTerm (.br created.1.1 [zeroed.1]) env created.2).2.vals.size = zeroed.2.vals.size + 1
        rw [emitTerm_run _ _ createdCurrent]
        simp only [created, newBlock1_run, Array.size_push]
      rw [size] at count
      omega
    have zeroGenerated : GeneratedBuilderState zeroed.2 := sampledGenerated.emitDef (env := env) (.constInt .i64 0) rfl
    have headerReady := frame.headerParameter (env := env) zeroGenerated.live live (zeroReady.2 live) closedExtension indexAllocated
    have indexReady : flowAt state.values index ≠ .pending := headerReady.2
    have createdGenerated : GeneratedBuilderState created.2 := zeroGenerated.newBlock (env := env) [.data (.int .i64)] rfl
    have freshBound : created.1.1 < created.2.blocks.size := by
      simp only [created, newBlock1_run, Array.size_push]
      exact Nat.lt_succ_self _
    have closedGenerated : GeneratedBuilderState closed := createdGenerated.emitTerm (env := env)
      (.br created.1.1 [zeroed.1]) (by
        intro target member
        have same : target = created.1.1 := by simpa [Term.successors] using member
        subst target
        exact freshBound) rfl
    have closing : created.2.Adv closed := adv_emitTerm (show emitTerm (.br created.1.1 [zeroed.1]) env created.2 = ((), closed) from rfl)
    have headerBound : created.1.1 < closed.blocks.size := Nat.lt_of_lt_of_le freshBound closing.ext.1
    have startedGenerated : GeneratedBuilderState started := closedGenerated.setCur (env := env) _ (by
      intro selected same
      have equal := Option.some.inj same
      subst selected
      exact headerBound) rfl
    have startedLive : started.cur.isSome = true := rfl
    have ownerAvailable : regrown.1 = true → flowAt state.values (owner.getD 0) ≠ .pending := by
      intro selected
      cases row : owner with
      | none => simp [regrown, regrowOf, row] at selected
      | some address => exact ownerReady address row beforeLive
    have sampledAvailable : regrown.1 = false → flowAt state.values sampled.1 ≠ .pending :=
      fun selected => sampleReady.2 selected sampleLive
    have toStarted : TypePrefix before started :=
      (types_regrowOf owner env before _ _ rfl).trans
        ((types_eachSampled regrown.1 view env regrown.2 _ _ rfl).trans
          ((types_emitDef (.constInt .i64 0) env sampled.2 _ _ rfl).trans
            ((types_newBlock [.data (.int .i64)] env zeroed.2 _ _ rfl).trans
              ((types_emitTerm (.br created.1.1 [zeroed.1]) env created.2 _ _ rfl).trans
                (types_setCur (some created.1.1) env closed _ _ rfl)))))
    obtain ⟨mu, originalView⟩ := viewRow beforeLive
    have actualView := toStarted view (.view mu element) originalView
    have originalIndex : created.2.vals[index]? = some (some (.data (.int .i64))) := by
      simp only [created, index, newBlock1_run, List.headD_cons, Array.getElem?_push_eq]
    have toCounter : TypePrefix created.2 started :=
      (types_emitTerm (.br created.1.1 [zeroed.1]) env created.2 _ _ rfl).trans
        (types_setCur (some created.1.1) env closed _ _ rfl)
    have actualIndex := toCounter index (.data (.int .i64)) originalIndex
    have loopReady := frame.eachLoop source startedGenerated headerBound startedLive visible flat actualView actualIndex
      (viewReady beforeLive) indexReady ownerAvailable sampledAvailable slotBound indexBound child
      iterExtension iterAllocated iterNative
    have resumed : EmitsOnly (ReadyOperands state) closed started := .of_blocks rfl
    rw [actual]
    exact prefixReady.trans (headerReady.1.trans (resumed.trans loopReady))

end Goose.Lower.Validation.ReplacementContentFlowSource

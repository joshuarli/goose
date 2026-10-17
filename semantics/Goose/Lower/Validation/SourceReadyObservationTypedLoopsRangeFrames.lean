import Goose.Lower.Validation.SourceReadyTypedStatementsRangeFrames
import Goose.Lower.Validation.SourceReadyObservationTypedLoopsRange

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

private theorem observed_range_tail {slot : VarId} {origin : OriginId} {body : Core.Block} (lower upper : ValueId) :
    AdvB (whenLive () fun _ => do
      let integer ← intTyOf lower
      let (header, parameters) ← newBlock [.data (.int integer)]
      let index := parameters.headD 0
      emitTerm (.br header [lower])
      setCur (some header)
      Lower.lowerRange integer index upper header (fun depth exit =>
        Lower.lowerBlock (some ⟨depth, exit, .next header integer index⟩) [(slot, index, origin)] false body)) := by
  refine advB_whenLive _ fun _ => AdvB.bind (advB_intTyOf lower) fun integer => ?_
  exact advB_header1 (.data (.int integer)) lower
    (tail := fun header index => Lower.lowerRange integer index upper header (fun depth exit =>
      Lower.lowerBlock (some ⟨depth, exit, .next header integer index⟩) [(slot, index, origin)] false body))
    (fun header index => advB_lowerRange integer index upper header (fun depth exit =>
      advB_lowerBlock (some ⟨depth, exit, .next header integer index⟩) [(slot, index, origin)] false body))

private theorem observed_types_range_tail {slot : VarId} {origin : OriginId} {body : Core.Block} (lower upper : ValueId) :
    TypeRun (whenLive () fun _ => do
      let integer ← intTyOf lower
      let (header, parameters) ← newBlock [.data (.int integer)]
      let index := parameters.headD 0
      emitTerm (.br header [lower])
      setCur (some header)
      Lower.lowerRange integer index upper header (fun depth exit =>
        Lower.lowerBlock (some ⟨depth, exit, .next header integer index⟩) [(slot, index, origin)] false body)) := by
  refine types_whenLive _ fun _ => TypeRun.bind (types_intTyOf lower) fun integer => ?_
  exact types_header1 (.data (.int integer)) lower
    (tail := fun header index => Lower.lowerRange integer index upper header (fun depth exit =>
      Lower.lowerBlock (some ⟨depth, exit, .next header integer index⟩) [(slot, index, origin)] false body))
    (fun header index => types_lowerRange integer index upper header (fun depth exit =>
      types_lowerBlock (some ⟨depth, exit, .next header integer index⟩) [(slot, index, origin)] false body))

theorem SourceReadyFrame.observedTypedRangeFrames {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS}
    {typingEnv output : TEnv} {results : List Ty} {loop : Option LoopCtx}
    {scope start finish : Nat} {origin : OriginId} {slot : VarId} {low high : Expr} {body : Core.Block}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyStmt typingEnv scope (.forRange slot low high body origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before) (slotCount : func.slots.size = typingEnv.vars.size)
    (native : SummaryPreservation.NativeRows types
      (lowerStmt loop (.forRange slot low high body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.forRange slot low high body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.forRange slot low high body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (lowChild : ∀ integer next last, Core.tyExpr typingEnv low next = .ok (.int integer, last) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows types (lowerExpr low (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerExpr low (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerExpr low (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state → ValueReadyAt state (lowerExpr low) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before (lowerExpr low (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (highChild : ∀ integer next last, Core.tyExpr typingEnv high next = .ok (.int integer, last) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let lower := lowerExpr low env before
      GeneratedBuilderState lower.2 → SummaryPreservation.NativeRows types (lowerExpr high env lower.2).2 →
      (lowerExpr high env lower.2).2.Ext completed → (lowerExpr high env lower.2).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state → ValueReadyAt state (lowerExpr high) env lower.2 ∧
      EmitsOnly (ReadyCallObservations module func state) lower.2 (lowerExpr high env lower.2).2)
    (bodyChild : ∀ type next (context : LoopCtx) (pre : List (SlotId × ValueId × OriginId)) initial,
      Core.tyBlock { typingEnv with loops := typingEnv.loops + 1, visible := slot :: typingEnv.visible }
        [] body next = .ok (type, finish) →
      GeneratedBuilderState initial → LoopBuilderTargets (some context) initial →
      SummaryPreservation.NativeRows types (Lower.lowerBlock (some context) pre false body (lowerEnv typingEnv.mod typingEnv.vars results) initial).2 →
      (Lower.lowerBlock (some context) pre false body (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.Ext completed →
      (Lower.lowerBlock (some context) pre false body (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady { typingEnv with loops := typingEnv.loops + 1, visible := slot :: typingEnv.visible } state →
      (∀ selected input org, (selected, input, org) ∈ pre → selected < func.slots.size) →
      (∀ selected input org, (selected, input, org) ∈ pre → flowAt state.values input ≠ .pending) →
      (∀ header integer index, context.cont = .next header integer index → flowAt state.values index ≠ .pending) →
      EmitsOnly (ReadyOperands state) initial (Lower.lowerBlock (some context) pre false body (lowerEnv typingEnv.mod typingEnv.vars results) initial).2 ∧
      EmitsOnly (ReadyCallObservations module func state) initial (Lower.lowerBlock (some context) pre false body (lowerEnv typingEnv.mod typingEnv.vars results) initial).2) :
    (EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.forRange slot low high body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.forRange slot low high body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before
        (lowerStmt loop (.forRange slot low high body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  obtain ⟨localVar, integer, lowerStart, lowerFinish, upperFinish, bodyType,
    declared, lowSource, highSource, _, bodySource, _⟩ := tyStmt_forRange_children source
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let lower := lowerExpr low env before
  let upper := lowerExpr high env lower.2
  have upperAdvance : upper.2.Adv (lowerStmt loop (.forRange slot low high body origin) env before).2 :=
    observed_range_tail (slot := slot) (origin := origin) (body := body) lower.1 upper.1 env upper.2 _ _ rfl
  have upperPrefix : TypePrefix upper.2 (lowerStmt loop (.forRange slot low high body origin) env before).2 :=
    observed_types_range_tail (slot := slot) (origin := origin) (body := body) lower.1 upper.1 env upper.2 _ _ rfl
  have upperExtension := upperAdvance.ext.trans extension
  have upperAllocated := Nat.le_trans upperAdvance.vals allocated
  have upperNative : SummaryPreservation.NativeRows types upper.2 := native.of_prefix upperPrefix
  have highAdvance := advB_lowerExpr high env lower.2 _ _ rfl
  have lowerNative : SummaryPreservation.NativeRows types lower.2 := upperNative.of_prefix (types_lowerExpr high env lower.2 _ _ rfl)
  have lowerGenerated : GeneratedBuilderState lower.2 := generated.lowerExpr low rfl
  have upperGenerated : GeneratedBuilderState upper.2 := lowerGenerated.lowerExpr high rfl
  have slotBound : slot < func.slots.size := by
    rw [slotCount]
    exact (Array.getElem?_eq_some_iff.mp (declare_ok _ _ _ _ _ declared).2.1).1
  refine frame.observedTypedRange source generated extension allocated visible
    (fun t first last checked => lowChild t first last checked generated lowerNative
      (highAdvance.ext.trans upperExtension) (Nat.le_trans highAdvance.vals upperAllocated) visible)
    (fun t first last checked => highChild t first last checked lowerGenerated upperNative upperExtension upperAllocated visible) ?_
  intro checkedType checkedStart checkedBlock binderVisible
  let integerType := (intTyOf lower.1 env upper.2).1
  let created := newBlock [.data (.int integerType)] env upper.2
  let index := created.1.2.headD 0
  let closed := (emitTerm (.br created.1.1 [lower.1]) env created.2).2
  let started := { closed with cur := some created.1.1 }
  let compared := Lower.emitDef (.cmp .lt integerType index upper.1) env started
  let forked := fork compared.1 env compared.2
  let selected := { forked.2 with cur := some forked.1.1 }
  change upper.2.cur.isSome = true → flowAt state.values index ≠ .pending → _
  intro live indexReady
  obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
  let context : LoopCtx := ⟨compared.2.stack.length, forked.1.2, .next created.1.1 integerType index⟩
  let doneBody := Lower.lowerBlock (some context) [(slot, index, origin)] false body env selected
  let back := Lower.rangeBack integerType index created.1.1 env doneBody.2
  let ranged := Lower.lowerRange integerType index upper.1 created.1.1
    (fun depth exit => Lower.lowerBlock (some ⟨depth, exit, .next created.1.1 integerType index⟩) [(slot, index, origin)] false body) env started
  have classifyRun : intTyOf lower.1 env upper.2 = (integerType, upper.2) := Prod.ext rfl (intTyOf_eq rfl)
  have actual : (lowerStmt loop (.forRange slot low high body origin) env before).2 = ranged.2 := by
    simp only [lowerStmt, bind_run]
    change (whenLive _ _ env upper.2).2 = _
    rw [whenLive_some _ _ _ current]
    change ((do
      let integer ← intTyOf lower.1
      let (header, parameters) ← newBlock [.data (.int integer)]
      let selectedIndex := parameters.headD 0
      emitTerm (.br header [lower.1])
      setCur (some header)
      Lower.lowerRange integer selectedIndex upper.1 header (fun depth exit =>
        Lower.lowerBlock (some ⟨depth, exit, .next header integer selectedIndex⟩)
          [(slot, selectedIndex, origin)] false body)) env upper.2).2 = ranged.2
    simp only [bind_run, classifyRun]
    rfl
  have ended : ranged.2 = { back.2 with cur := some forked.1.2 } := rfl
  have backExtension : back.2.Ext completed := by have h := extension; rw [actual, ended] at h; exact h
  have backNative : SummaryPreservation.NativeRows types back.2 := by have h := native; rw [actual, ended] at h; exact h
  have backCount : back.2.vals.size ≤ completed.vals.size := by have h := allocated; rw [actual, ended] at h; exact h
  have backAdvance := advB_rangeBack integerType index created.1.1 env doneBody.2 _ _ rfl
  have bodyNative := backNative.of_prefix (types_rangeBack integerType index created.1.1 env doneBody.2 _ _ rfl)
  have createdGenerated : GeneratedBuilderState created.2 := upperGenerated.newBlock [.data (.int integerType)] (env := env) rfl
  have createdBound : created.1.1 < created.2.blocks.size := by simp only [created, newBlock1_run, Array.size_push]; exact Nat.lt_succ_self _
  have closedGenerated : GeneratedBuilderState closed := createdGenerated.emitTerm (.br created.1.1 [lower.1])
    (by
      intro target member
      have same : target = created.1.1 := by simpa [Term.successors] using member
      exact same ▸ createdBound) (env := env) rfl
  have headerBound : created.1.1 < closed.blocks.size := Nat.lt_of_lt_of_le createdBound
    (advB_emitTerm (.br created.1.1 [lower.1]) env created.2 _ _ rfl).ext.1
  have startedGenerated : GeneratedBuilderState started := closedGenerated.setCur (some created.1.1) (env := env)
    (by intro target row; cases row; exact headerBound) rfl
  have comparedGenerated : GeneratedBuilderState compared.2 := startedGenerated.emitDef (.cmp .lt integerType index upper.1) (env := env) rfl
  have forkGenerated : GeneratedBuilderState forked.2 := comparedGenerated.fork compared.1 (env := env) rfl
  have comparedCurrent : compared.2.cur = some created.1.1 := by rw [ready_def_current]
  have targetBounds := liveBound_fork comparedCurrent compared.1 env
  have selectedGenerated : GeneratedBuilderState selected := forkGenerated.setCur (some forked.1.1) (env := env)
    (by intro target row; cases row; exact targetBounds.1) rfl
  have bodyTargets : LoopBuilderTargets (some context) selected := by
    constructor
    · exact targetBounds.2
    · exact Nat.lt_of_lt_of_le headerBound (Nat.le_trans
        (advB_emitDef (.cmp .lt integerType index upper.1) env started _ _ rfl).ext.1
        (advB_fork compared.1 env compared.2 _ _ rfl).ext.1)
  exact bodyChild checkedType checkedStart context [(slot, index, origin)] selected checkedBlock selectedGenerated bodyTargets bodyNative
    (backAdvance.ext.trans backExtension) (Nat.le_trans backAdvance.vals backCount) binderVisible
    (by intro s v o member; have same : s = slot := congrArg Prod.fst (List.mem_singleton.mp member); exact same ▸ slotBound)
    (by intro s v o member; have same : v = index := congrArg (fun p => p.2.1) (List.mem_singleton.mp member); exact same ▸ indexReady)
    (by intro header integer value same; cases same; exact indexReady)

end Goose.Lower.Validation.ReplacementContentFlowSource

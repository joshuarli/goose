import Goose.Lower.Validation.SourceReadyTypedStatementsWhileFrames
import Goose.Lower.Validation.SourceReadyObservationLoopsStatements

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.observedTypedWhileStatement {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS}
    {typingEnv output : TEnv} {results : List Ty} {loop : Option LoopCtx}
    {scope start finish : Nat} {origin : OriginId} {condition : Expr} {body : Core.Block}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyStmt typingEnv scope (.while condition body origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows types
      (lowerStmt loop (.while condition body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerStmt loop (.while condition body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.while condition body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (conditionChild : ∀ next, Core.tyExpr typingEnv condition start = .ok (.bool, next) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let created := newBlock [] env before
      let closed := (emitTerm (.br created.1.1 []) env created.2).2
      let selected := { closed with cur := some created.1.1 }
      GeneratedBuilderState selected →
      SummaryPreservation.NativeRows types (lowerExpr condition env selected).2 →
      (lowerExpr condition env selected).2.Ext completed →
      (lowerExpr condition env selected).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state → ValueReadyAt state (lowerExpr condition) env selected ∧
      EmitsOnly (ReadyCallObservations module func state) selected (lowerExpr condition env selected).2)
    (bodyChild : ∀ type next (context : LoopCtx) initial,
      Core.tyBlock { typingEnv with loops := typingEnv.loops + 1 } [] body next = .ok (type, finish) →
      GeneratedBuilderState initial → LoopBuilderTargets (some context) initial →
      SummaryPreservation.NativeRows types (Lower.lowerBlock (some context) [] false body
        (lowerEnv typingEnv.mod typingEnv.vars results) initial).2 →
      (Lower.lowerBlock (some context) [] false body (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.Ext completed →
      (Lower.lowerBlock (some context) [] false body (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady { typingEnv with loops := typingEnv.loops + 1 } state →
      (∀ header integer index, context.cont = .next header integer index → flowAt state.values index ≠ .pending) →
      EmitsOnly (ReadyOperands state) initial (Lower.lowerBlock (some context) [] false body
        (lowerEnv typingEnv.mod typingEnv.vars results) initial).2 ∧
      EmitsOnly (ReadyCallObservations module func state) initial (Lower.lowerBlock (some context) [] false body
        (lowerEnv typingEnv.mod typingEnv.vars results) initial).2) :
    (EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.while condition body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.while condition body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before
        (lowerStmt loop (.while condition body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  obtain ⟨next, bodyType, conditionSource, bodySource, _⟩ := tyStmt_while_children source
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let created := newBlock [] env before
  let closed := (emitTerm (.br created.1.1 []) env created.2).2
  let started := { closed with cur := some created.1.1 }
  let tested := lowerExpr condition env started
  let bodyAction := fun depth exit => Lower.lowerBlock (some ⟨depth, exit, .jump created.1.1⟩) [] false body
  let action := Lower.lowerWhile created.1.1 (lowerExpr condition) bodyAction
  have actual : (lowerStmt loop (.while condition body origin) env before).2 = (action env started).2 := rfl
  have finalExtension : (action env started).2.Ext completed := actual ▸ extension
  have finalNative : SummaryPreservation.NativeRows types (action env started).2 := actual ▸ native
  have finalCount : (action env started).2.vals.size ≤ completed.vals.size := actual ▸ allocated
  have createdGenerated : GeneratedBuilderState created.2 := generated.newBlock [] (env := env) rfl
  have createdBound : created.1.1 < created.2.blocks.size := by simp only [created, newBlock0_run, Array.size_push]; exact Nat.lt_succ_self _
  have closedGenerated : GeneratedBuilderState closed := createdGenerated.emitTerm (.br created.1.1 [])
    (by
      intro target member
      have same : target = created.1.1 := by simpa [Term.successors] using member
      exact same ▸ createdBound)
    (env := env) rfl
  have headerBound : created.1.1 < closed.blocks.size :=
    Nat.lt_of_lt_of_le createdBound (advB_emitTerm (.br created.1.1 []) env created.2 _ _ rfl).ext.1
  have startedGenerated : GeneratedBuilderState started := closedGenerated.setCur (some created.1.1) (env := env)
    (by intro target row; cases row; exact headerBound) rfl
  have tailAdvance : tested.2.Adv (action env started).2 :=
    (advB_whenLive () fun _ => advB_loopBody tested.1 (fun _ _ => advB_lowerBlock _ [] false body) (advB_emitTerm (.br created.1.1 [])))
      env tested.2 _ _ rfl
  have tailTypes : TypePrefix tested.2 (action env started).2 :=
    (types_whenLive () fun _ => types_loopBody tested.1 (fun _ _ => types_lowerBlock _ [] false body) (types_emitTerm (.br created.1.1 [])))
      env tested.2 _ _ rfl
  have conditionPair := conditionChild next conditionSource startedGenerated (finalNative.of_prefix tailTypes)
    (tailAdvance.ext.trans finalExtension) (Nat.le_trans tailAdvance.vals finalCount) visible
  have bodyPair : ∀ type next,
      Core.tyBlock { typingEnv with loops := typingEnv.loops + 1 } [] body next = .ok (type, finish) →
      VisibleSlotsReady { typingEnv with loops := typingEnv.loops + 1 } state →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let created := newBlock [] env before
      let closed := (emitTerm (.br created.1.1 []) env created.2).2
      let started := { closed with cur := some created.1.1 }
      let evaluated := lowerExpr condition env started
      let forked := fork evaluated.1 env evaluated.2
      let selected := { forked.2 with cur := some forked.1.1 }
      evaluated.2.cur.isSome = true →
      EmitsOnly (ReadyOperands state) selected
        (Lower.lowerBlock (some ⟨evaluated.2.stack.length, forked.1.2, .jump created.1.1⟩) [] false body env selected).2 ∧
      EmitsOnly (ReadyCallObservations module func state) selected
        (Lower.lowerBlock (some ⟨evaluated.2.stack.length, forked.1.2, .jump created.1.1⟩) [] false body env selected).2 := by
    intro checkedType checkedStart checkedSource loopVisible
    change tested.2.cur.isSome = true → _
    intro live
    obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
    let forked := fork tested.1 env tested.2
    let selected := { forked.2 with cur := some forked.1.1 }
    let context : LoopCtx := ⟨tested.2.stack.length, forked.1.2, .jump created.1.1⟩
    let doneBody := Lower.lowerBlock (some context) [] false body env selected
    let back := (emitTerm (.br created.1.1 []) env doneBody.2).2
    have ended : (action env started).2 = { back with cur := some forked.1.2 } := by
      simp only [action, Lower.lowerWhile, bind_run]
      change (whenLive _ _ env tested.2).2 = _
      rw [whenLive_some _ _ _ current]
      rfl
    have backExtension : back.Ext completed := by have h := finalExtension; rw [ended] at h; exact h
    have backNative : SummaryPreservation.NativeRows types back := by have h := finalNative; rw [ended] at h; exact h
    have backCount : back.vals.size ≤ completed.vals.size := by have h := finalCount; rw [ended] at h; exact h
    have backAdvance := advB_emitTerm (.br created.1.1 []) env doneBody.2 _ _ rfl
    have doneNative := backNative.of_prefix (types_emitTerm (.br created.1.1 []) env doneBody.2 _ _ rfl)
    have testedGenerated : GeneratedBuilderState tested.2 := startedGenerated.lowerExpr condition rfl
    have forkGenerated : GeneratedBuilderState forked.2 := testedGenerated.fork tested.1 (env := env) rfl
    have targetBounds := liveBound_fork current tested.1 env
    have selectedGenerated : GeneratedBuilderState selected := forkGenerated.setCur (some forked.1.1) (env := env)
      (by intro target row; cases row; exact targetBounds.1) rfl
    have bodyTargets : LoopBuilderTargets (some context) selected := by
      constructor
      · exact targetBounds.2
      · exact Nat.lt_of_lt_of_le headerBound
          (Nat.le_trans (advB_lowerExpr condition env started _ _ rfl).ext.1 (advB_fork tested.1 env tested.2 _ _ rfl).ext.1)
    exact bodyChild checkedType checkedStart context selected checkedSource selectedGenerated bodyTargets doneNative
      (backAdvance.ext.trans backExtension) (Nat.le_trans backAdvance.vals backCount) loopVisible
      (by intro header integer index impossible; cases impossible)
  have semantic := typed_ready_while (loop := loop) source visible (fun _ _ => conditionPair.1)
    (fun type next checked ready live => (bodyPair type next checked ready live).1)
  refine ⟨semantic, ?_⟩
  exact observation_whileStatement loop condition body origin conditionPair.2
    (fun live => (bodyPair bodyType next bodySource visible live).2)

end Goose.Lower.Validation.ReplacementContentFlowSource

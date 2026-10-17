import Goose.Lower.Validation.SourceReadyTypedStatementsRange
import Goose.Lower.Validation.SourceReadyObservationLoopsStatements

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.observedTypedRange {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS}
    {typingEnv output : TEnv} {results : List Ty} {loop : Option LoopCtx}
    {scope start finish : Nat} {origin : OriginId} {slot : VarId} {low high : Expr} {body : Core.Block}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyStmt typingEnv scope (.forRange slot low high body origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (extension : (lowerStmt loop (.forRange slot low high body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.forRange slot low high body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (lowChild : ∀ integer next last, Core.tyExpr typingEnv low next = .ok (.int integer, last) →
      ValueReadyAt state (lowerExpr low) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations module func state) before
        (lowerExpr low (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (highChild : ∀ integer next last, Core.tyExpr typingEnv high next = .ok (.int integer, last) →
      ValueReadyAt state (lowerExpr high) (lowerEnv typingEnv.mod typingEnv.vars results)
        (lowerExpr low (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      EmitsOnly (ReadyCallObservations module func state) (lowerExpr low (lowerEnv typingEnv.mod typingEnv.vars results) before).2
        (lowerExpr high (lowerEnv typingEnv.mod typingEnv.vars results)
          (lowerExpr low (lowerEnv typingEnv.mod typingEnv.vars results) before).2).2)
    (bodyChild : ∀ bodyType next,
      Core.tyBlock { typingEnv with loops := typingEnv.loops + 1, visible := slot :: typingEnv.visible }
        [] body next = .ok (bodyType, finish) →
      VisibleSlotsReady { typingEnv with loops := typingEnv.loops + 1, visible := slot :: typingEnv.visible } state →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let lower := lowerExpr low env before
      let upper := lowerExpr high env lower.2
      let integerType := (intTyOf lower.1 env upper.2).1
      let created := newBlock [.data (.int integerType)] env upper.2
      let index := created.1.2.headD 0
      let closed := (emitTerm (.br created.1.1 [lower.1]) env created.2).2
      let started := { closed with cur := some created.1.1 }
      let compared := Lower.emitDef (.cmp .lt integerType index upper.1) env started
      let forked := fork compared.1 env compared.2
      let selected := { forked.2 with cur := some forked.1.1 }
      upper.2.cur.isSome = true → flowAt state.values index ≠ .pending →
      EmitsOnly (ReadyOperands state) selected
        (Lower.lowerBlock (some ⟨compared.2.stack.length, forked.1.2, .next created.1.1 integerType index⟩)
          [(slot, index, origin)] false body env selected).2 ∧
      EmitsOnly (ReadyCallObservations module func state) selected
        (Lower.lowerBlock (some ⟨compared.2.stack.length, forked.1.2, .next created.1.1 integerType index⟩)
          [(slot, index, origin)] false body env selected).2) :
    (EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.forRange slot low high body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.forRange slot low high body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state)) ∧
      EmitsOnly (ReadyCallObservations module func state) before
        (lowerStmt loop (.forRange slot low high body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  obtain ⟨localVar, integer, lowerStart, lowerFinish, upperFinish, bodyType,
    declared, lowSource, highSource, binderType, bodySource, outputEq⟩ := tyStmt_forRange_children source
  subst output
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let lower := lowerExpr low env before
  let upper := lowerExpr high env lower.2
  have lowerPair := lowChild integer lowerStart lowerFinish lowSource
  have upperPair := highChild integer lowerFinish upperFinish highSource
  have lowerReady := lowerPair.1
  have upperReady := upperPair.1
  have binderVisible := visible.declareScalar (declare_ok _ _ _ _ _ declared).2.1
    (by simp only [binderType, Ty.isRefLike])
  cases current : upper.2.cur with
  | none =>
    refine ⟨⟨?_, fun _ => visible⟩, ?_⟩
    simp only [lowerStmt, bind_run]
    rw [whenLive_none _ _ _ current]
    exact lowerReady.1.trans upperReady.1
    simp only [lowerStmt, bind_run]
    rw [whenLive_none _ _ _ current]
    exact lowerPair.2.trans upperPair.2
  | some block =>
    have live : upper.2.cur.isSome = true := by simp [current]
    let integerType := (intTyOf lower.1 env upper.2).1
    let created := newBlock [.data (.int integerType)] env upper.2
    let index := created.1.2.headD 0
    let closed := (emitTerm (.br created.1.1 [lower.1]) env created.2).2
    let started := { closed with cur := some created.1.1 }
    let action := fun depth exit => Lower.lowerBlock (some ⟨depth, exit, .next created.1.1 integerType index⟩)
      [(slot, index, origin)] false body
    let ranged := Lower.lowerRange integerType index upper.1 created.1.1 action env started
    have classified : (intTyOf lower.1 env upper.2).2 = upper.2 := intTyOf_eq rfl
    have actual : (lowerStmt loop (.forRange slot low high body origin) env before).2 = ranged.2 := by
      simp only [lowerStmt, bind_run]
      rw [whenLive_some _ _ _ current]
      change ((do
        let type ← intTyOf lower.1
        let (header, parameters) ← newBlock [.data (.int type)]
        emitTerm (.br header [lower.1])
        setCur (some header)
        Lower.lowerRange type (parameters.headD 0) upper.1 header
          (fun depth exit => Lower.lowerBlock (some ⟨depth, exit, .next header type (parameters.headD 0)⟩)
            [(slot, parameters.headD 0, origin)] false body) : B Unit) env upper.2).2 = ranged.2
      have classifyRun : intTyOf lower.1 env upper.2 = (integerType, upper.2) := Prod.ext rfl classified
      simp only [bind_run, classifyRun]
      rfl
    have rangeExtension : ranged.2.Ext completed := actual ▸ extension
    have rangeAllocated : ranged.2.vals.size ≤ completed.vals.size := actual ▸ allocated
    have rangeAdvance : started.Adv ranged.2 := advB_lowerRange integerType index upper.1 created.1.1
      (fun depth exit => advB_lowerBlock _ _ _ body) env started _ _ rfl
    have closedExtension : closed.Ext completed :=
      ((EmitsOnly.of_blocks (property := ReadyOperands state) rfl).extension : closed.Ext started).trans
        (rangeAdvance.ext.trans rangeExtension)
    have createdCurrent : created.2.cur = some block := current
    have indexAllocated : upper.2.vals.size < completed.vals.size := by
      have count := Nat.le_trans rangeAdvance.vals rangeAllocated
      have equal : started.vals.size = upper.2.vals.size + 1 := by
        change (emitTerm (.br created.1.1 [lower.1]) env created.2).2.vals.size = upper.2.vals.size + 1
        rw [emitTerm_run _ _ createdCurrent]
        simp only [created, newBlock1_run, Array.size_push]
      rw [equal] at count
      omega
    have upperGenerated : GeneratedBuilderState upper.2 := (generated.lowerExpr low rfl).lowerExpr high rfl
    have headerReady := frame.headerParameter (bounded := upperGenerated.live)
      (live := live) (available := lowerReady.2 ((dead_lowerExpr high).live_before rfl live)) closedExtension indexAllocated
    have indexReady : flowAt state.values index ≠ .pending := headerReady.2
    have headerLive : started.cur.isSome = true := rfl
    have headerBound : LiveBound started := by
      apply liveBound_setCur (state := closed) (env := env)
      have blockSize : closed.blocks.size = created.2.blocks.size := by
        rw [show closed = (emitTerm (.br created.1.1 [lower.1]) env created.2).2 from rfl]
        simp only [emitTerm_run _ _ createdCurrent, Array.size_modify]
      rw [blockSize]
      simp only [created, newBlock1_run, Array.size_push]
      exact Nat.lt_succ_self _
    have bodyPair := bodyChild bodyType upperFinish bodySource binderVisible live indexReady
    have rangeReady := frame.lowerRange rangeExtension rangeAllocated headerBound headerLive indexReady (upperReady.2 live)
      (fun depth exit => advB_lowerBlock _ _ _ body)
      bodyPair.1
    have startReady : EmitsOnly (ReadyOperands state) closed started := .of_blocks rfl
    refine ⟨⟨?_, fun _ => visible⟩, ?_⟩
    rw [actual]
    exact lowerReady.1.trans (upperReady.1.trans (headerReady.1.trans (startReady.trans rangeReady)))
    rw [actual]
    have createdObserved := emitsOnly_newBlock (ReadyCallObservations module func state)
      [.data (.int integerType)] env upper.2 _ _ rfl
    have closedObserved := observation_term (module := module) (func := func) (state := state)
      (.br created.1.1 [lower.1]) env created.2 _ _ rfl
    have startedObserved : EmitsOnly (ReadyCallObservations module func state) closed started := .of_blocks rfl
    have rangeObserved := observation_range (le := env) (before := started)
      integerType index upper.1 created.1.1 action bodyPair.2
    exact lowerPair.2.trans (upperPair.2.trans (createdObserved.trans
      (closedObserved.trans (startedObserved.trans rangeObserved))))

end Goose.Lower.Validation.ReplacementContentFlowSource

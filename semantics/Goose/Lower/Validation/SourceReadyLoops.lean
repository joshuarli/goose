import Goose.Lower.Validation.SourceReadyControlShortCircuit
import Goose.Lower.Validation.SourceReadyControlBranches

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem ready_loopBody {state : State} {env : LEnv} {before : LS} {condition : ValueId}
    {body : Nat → BlockId → B ValueId} {back : B Unit}
    (available : flowAt state.values condition ≠ .pending)
    (child :
      let forked := fork condition env before
      let started := { forked.2 with cur := some forked.1.1 }
      EmitsOnly (ReadyOperands state) started (body before.stack.length forked.1.2 env started).2)
    (returning :
      let forked := fork condition env before
      let evaluated := body before.stack.length forked.1.2 env { forked.2 with cur := some forked.1.1 }
      EmitsOnly (ReadyOperands state) evaluated.2 (back env evaluated.2).2) :
    EmitsOnly (ReadyOperands state) before (loopBody condition body back env before).2 := by
  let forked := fork condition env before
  let started := { forked.2 with cur := some forked.1.1 }
  let evaluated := body before.stack.length forked.1.2 env started
  have forkReady := ready_fork (env := env) (before := before) (fun _ => available)
  have startedReady : EmitsOnly (ReadyOperands state) forked.2 started := .of_blocks rfl
  have allReady := forkReady.trans (startedReady.trans (child.trans returning))
  exact allReady.trans (.of_blocks rfl)

theorem ready_lowerWhile {state : State} {env : LEnv} {before : LS} {header : BlockId}
    {condition : B ValueId} {body : Nat → BlockId → B ValueId}
    (conditionReady : ValueReadyAt state condition env before)
    (child : (condition env before).2.cur.isSome = true →
      let current := (condition env before).2
      let forked := fork (condition env before).1 env current
      let started := { forked.2 with cur := some forked.1.1 }
      EmitsOnly (ReadyOperands state) started (body current.stack.length forked.1.2 env started).2) :
    EmitsOnly (ReadyOperands state) before (lowerWhile header condition body env before).2 := by
  cases current : (condition env before).2.cur with
  | none =>
    simpa only [lowerWhile, bind_run, whenLive_none _ _ _ current, pure_run] using conditionReady.1
  | some block =>
    have live : (condition env before).2.cur.isSome = true := by simp [current]
    have loopReady := ready_loopBody (back := emitTerm (.br header [])) (conditionReady.2 live) (child live) (by
      exact ready_emitTerm rfl (by intro _ value member; simp [Inst.uses, Term.uses] at member))
    simpa only [lowerWhile, bind_run, whenLive_some _ _ _ current] using conditionReady.1.trans loopReady

theorem SourceReadyFrame.rangeBack {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {integerType : IntTy} {index : ValueId} {header : BlockId}
    (frame : SourceReadyFrame module callees func types state completed)
    (extension : (Goose.Lower.rangeBack integerType index header env before).2.Ext completed)
    (allocated : (Goose.Lower.rangeBack integerType index header env before).2.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before)
    (available : before.cur.isSome = true → flowAt state.values index ≠ .pending) :
    EmitsOnly (ReadyOperands state) before (Goose.Lower.rangeBack integerType index header env before).2 := by
  cases current : before.cur with
  | none =>
    simp only [Goose.Lower.rangeBack, bind_run, isLive_none current, Bool.false_eq_true, reduceIte, pure_run]
    exact .refl _ _
  | some block =>
    let incremented := Goose.Lower.emitDef (.next integerType index) env before
    let closed := (emitTerm (.br header [incremented.1]) env incremented.2).2
    have active := isLive_run (le := env) current
    have tail := adv_emitTerm (show emitTerm (.br header [incremented.1]) env incremented.2 = ((), closed) from rfl)
    have nextExtension : incremented.2.Ext completed := tail.ext.trans (by
      simpa only [Goose.Lower.rangeBack, bind_run, active, reduceIte] using extension)
    have nextBound : incremented.2.vals.size ≤ completed.vals.size := Nat.le_trans tail.vals (by
      simpa only [Goose.Lower.rangeBack, bind_run, active, reduceIte] using allocated)
    have nextReady := frame.emitDef (show Goose.Lower.emitDef (.next integerType index) env before = incremented from rfl)
      nextExtension nextBound bounded (by
        intro live operand member
        have same : operand = index := by simpa [Op.uses] using member
        subst operand
        exact available live)
      (by intro _ address impossible; cases impossible) (by intro _ fn args origin impossible; cases impossible)
    have closedReady : EmitsOnly (ReadyOperands state) incremented.2 closed := ready_emitTerm rfl (by
      intro live operand member
      have same : operand = incremented.1 := by simpa [Inst.uses, Term.uses] using member
      subst operand
      exact nextReady.2 live)
    simpa only [Goose.Lower.rangeBack, bind_run, active, reduceIte] using nextReady.1.trans closedReady

theorem SourceReadyFrame.lowerRange {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {integerType : IntTy} {index bound : ValueId} {header : BlockId}
    {body : Nat → BlockId → B ValueId}
    (frame : SourceReadyFrame module callees func types state completed)
    (extension : (Goose.Lower.lowerRange integerType index bound header body env before).2.Ext completed)
    (allocated : (Goose.Lower.lowerRange integerType index bound header body env before).2.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before) (live : before.cur.isSome = true)
    (indexReady : flowAt state.values index ≠ .pending)
    (boundReady : flowAt state.values bound ≠ .pending)
    (advance : ∀ depth exit, AdvB (body depth exit))
    (child :
      let compared := Goose.Lower.emitDef (.cmp .lt integerType index bound) env before
      let forked := fork compared.1 env compared.2
      let started := { forked.2 with cur := some forked.1.1 }
      EmitsOnly (ReadyOperands state) started (body compared.2.stack.length forked.1.2 env started).2) :
    EmitsOnly (ReadyOperands state) before
      (Goose.Lower.lowerRange integerType index bound header body env before).2 := by
  let compared := Goose.Lower.emitDef (.cmp .lt integerType index bound) env before
  let forked := fork compared.1 env compared.2
  let started := { forked.2 with cur := some forked.1.1 }
  let evaluated := body compared.2.stack.length forked.1.2 env started
  let returned := (Goose.Lower.rangeBack integerType index header env evaluated.2).2
  have tail := advB_loopBody compared.1 advance (advB_rangeBack integerType index header)
    env compared.2 _ _ rfl
  have compareExtension : compared.2.Ext completed := tail.ext.trans extension
  have compareBound : compared.2.vals.size ≤ completed.vals.size := Nat.le_trans tail.vals allocated
  have compareReady := frame.emitDef (show Goose.Lower.emitDef (.cmp .lt integerType index bound) env before = compared from rfl)
    compareExtension compareBound bounded (by
      intro _ operand member
      rcases (show operand = index ∨ operand = bound from by simpa [Op.uses] using member) with h | h
      · subst operand; exact indexReady
      · subst operand; exact boundReady)
    (by intro _ address impossible; cases impossible) (by intro _ fn args origin impossible; cases impossible)
  have compareLive : compared.2.cur.isSome = true := by
    obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
    simp only [compared, emitDef_run _ _ current]
    exact live
  have forkIds : forked.1 = (compared.2.blocks.size, compared.2.blocks.size + 1) ∧
      forked.2.blocks.size = compared.2.blocks.size + 2 := fork_ids rfl
  have startedBound : LiveBound started := by
    apply liveBound_setCur (state := forked.2) (env := env)
    have id := congrArg Prod.fst forkIds.1
    have size := forkIds.2
    nat_omega
  have evaluatedBound := liveBound_of_advB (advance compared.2.stack.length forked.1.2) env started startedBound
  have returnedExtension : returned.Ext completed := by
    have finalExt : returned.Ext (Goose.Lower.lowerRange integerType index bound header body env before).2 := by
      apply (EmitsOnly.of_blocks (property := ReadyOperands state) ?_).extension
      rfl
    exact finalExt.trans extension
  have returnedAllocated : returned.vals.size ≤ completed.vals.size := allocated
  have returnReady := frame.rangeBack returnedExtension returnedAllocated evaluatedBound (fun _ => indexReady)
  have loopReady := ready_loopBody (compareReady.2 compareLive) child returnReady
  exact compareReady.1.trans loopReady

theorem SourceReadyFrame.eachLen {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {regrow : Bool} {owner : Option ValueId} {sampled : ValueId}
    (frame : SourceReadyFrame module callees func types state completed)
    (extension : (Goose.Lower.eachLen regrow owner sampled env before).2.Ext completed)
    (allocated : (Goose.Lower.eachLen regrow owner sampled env before).2.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before)
    (ownerReady : regrow = true → before.cur.isSome = true → flowAt state.values (owner.getD 0) ≠ .pending)
    (sampleReady : regrow = false → before.cur.isSome = true → flowAt state.values sampled ≠ .pending) :
    ValueReadyAt state (Goose.Lower.eachLen regrow owner sampled) env before := by
  cases regrow with
  | false => exact ⟨.refl _ _, sampleReady rfl⟩
  | true =>
    exact frame.emitDef rfl extension allocated bounded (by
      intro live operand member
      have same : operand = owner.getD 0 := by simpa [Op.uses] using member
      subst operand
      exact ownerReady rfl live)
      (by intro _ address impossible; cases impossible) (by intro _ fn args origin impossible; cases impossible)

theorem SourceReadyFrame.lowerEach {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {regrow : Bool} {owner : Option ValueId} {sampled index : ValueId} {header : BlockId}
    {body : Nat → BlockId → B ValueId}
    (frame : SourceReadyFrame module callees func types state completed)
    (extension : (Goose.Lower.lowerEach regrow owner sampled header index body env before).2.Ext completed)
    (allocated : (Goose.Lower.lowerEach regrow owner sampled header index body env before).2.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before) (live : before.cur.isSome = true)
    (indexReady : flowAt state.values index ≠ .pending)
    (ownerReady : regrow = true → flowAt state.values (owner.getD 0) ≠ .pending)
    (sampleReady : regrow = false → flowAt state.values sampled ≠ .pending)
    (advance : ∀ depth exit, AdvB (body depth exit))
    (child :
      let length := Goose.Lower.eachLen regrow owner sampled env before
      let compared := Goose.Lower.emitDef (.cmp .lt .i64 index length.1) env length.2
      let forked := fork compared.1 env compared.2
      let started := { forked.2 with cur := some forked.1.1 }
      EmitsOnly (ReadyOperands state) started (body compared.2.stack.length forked.1.2 env started).2) :
    EmitsOnly (ReadyOperands state) before
      (Goose.Lower.lowerEach regrow owner sampled header index body env before).2 := by
  let length := Goose.Lower.eachLen regrow owner sampled env before
  have tail := advB_lowerRange .i64 index length.1 header advance env length.2 _ _ rfl
  have lengthExtension : length.2.Ext completed := tail.ext.trans extension
  have lengthAllocated : length.2.vals.size ≤ completed.vals.size := Nat.le_trans tail.vals allocated
  have lengthReady := frame.eachLen lengthExtension lengthAllocated bounded
    (fun selected _ => ownerReady selected) (fun selected _ => sampleReady selected)
  have lengthBound := liveBound_of_advB (advB_eachLen regrow owner sampled) env before bounded
  have lengthLive : length.2.cur.isSome = true := by
    cases regrow with
    | false => exact live
    | true =>
      obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
      simp only [length, Goose.Lower.eachLen, reduceIte, emitDef_run _ _ current]
      exact live
  have rangeReady := frame.lowerRange extension allocated lengthBound lengthLive indexReady
    (lengthReady.2 lengthLive) advance child
  exact lengthReady.1.trans rangeReady

#print axioms SourceReadyFrame.lowerRange
#print axioms SourceReadyFrame.eachLen
#print axioms SourceReadyFrame.lowerEach

#print axioms ready_loopBody
#print axioms ready_lowerWhile
#print axioms SourceReadyFrame.rangeBack

end Goose.Lower.Validation.ReplacementContentFlowSource

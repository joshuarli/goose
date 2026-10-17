import Goose.Lower.Validation.CfgGeneratedEdgeShortCircuit
import Goose.Lower.Validation.CfgGeneratedEdgeScalar

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def ContinueEdgeArguments (continuation : ContKind) (state : LS) : Prop :=
  match continuation with
  | .jump header => EdgeArguments state header []
  | .next header ty counter => CounterHeader state header ty counter ∧
      state.vals[counter]? = some (some (.data (.int ty)))

theorem ContinueEdgeArguments.extend {continuation : ContKind} {before after : LS}
    (extension : EdgeExtension before after) (frame : ContinueEdgeArguments continuation before) :
    ContinueEdgeArguments continuation after := by
  cases continuation with
  | jump header => exact EdgeArguments.extend extension frame
  | next header ty counter => exact ⟨frame.1.extend extension, extension.types _ _ frame.2⟩

theorem generated_edge_loopBody_at (env : LEnv) (context : Option LoopCtx) (condition : ValueId)
    (continuation : ContKind) {body : Nat → BlockId → B ValueId} {back : B Unit}
    (bodyEdges : ∀ depth exit, GeneratedEdgeRun env (some ⟨depth, exit, continuation⟩) (body depth exit))
    (backEdges : ∀ depth exit, GeneratedEdgeRun env (some ⟨depth, exit, continuation⟩) back)
    (before after : LS) (result : Unit)
    (run : loopBody condition body back env before = (result, after))
    (generated : GeneratedBuilderState before) (loop : LoopEdgeArguments context before)
    (checked : BuilderEdgeArguments before) (current : before.cur.isSome = true)
    (frame : ContinueEdgeArguments continuation before) :
    GeneratedBuilderState after ∧ EdgeExtension before after ∧ BuilderEdgeArguments after := by
  simp only [loopBody, bind_eq] at run
  obtain ⟨snapshot, readState, readRun, ⟨bodyBlock, exit⟩, forked, forkRun,
    ignored, selected, selectRun, bodyValue, bodyEnd, bodyRun, ignored', backed, backRun, finalRun⟩ := run
  change (before, before) = (snapshot, readState) at readRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj readRun
  obtain ⟨block, blockCurrent⟩ : ∃ block, before.cur = some block := by
    cases equal : before.cur with
    | none => simp [equal] at current
    | some block => exact ⟨block, rfl⟩
  obtain ⟨forkGenerated, forkExtension, forkChecked⟩ :=
    generated_edge_fork env context condition before _ forked forkRun generated loop checked
  have forkArguments := edgeArguments_fork blockCurrent (generated.live block blockCurrent) condition env
  rw [forkRun] at forkArguments
  have bodyEdge : EdgeArguments forked bodyBlock [] := forkArguments.1
  have exitEdge : EdgeArguments forked exit [] := forkArguments.2
  obtain ⟨selectedGenerated, selectExtension, selectedChecked⟩ :=
    generated_edge_setCur_at (some bodyBlock) env forked selected ignored selectRun forkGenerated forkChecked
      (by intro target same; have equal := Option.some.inj same; simpa [← equal] using bodyEdge.bound)
  have beforeBody := forkExtension.trans selectExtension
  have innerLoop : LoopEdgeArguments (some ⟨before.stack.length, exit, continuation⟩) selected :=
    ⟨exitEdge.extend selectExtension, frame.extend beforeBody⟩
  obtain ⟨bodyGenerated, bodyExtension, bodyChecked⟩ :=
    bodyEdges before.stack.length exit selected bodyValue bodyEnd bodyRun selectedGenerated innerLoop selectedChecked
  obtain ⟨backGenerated, backExtension, backChecked⟩ :=
    backEdges before.stack.length exit bodyEnd ignored' backed backRun bodyGenerated
      (innerLoop.extend bodyExtension) bodyChecked
  have exitStill := exitEdge.extend (selectExtension.trans (bodyExtension.trans backExtension))
  obtain ⟨afterGenerated, finalExtension, afterChecked⟩ :=
    generated_edge_setCur_at (some exit) env backed after result finalRun backGenerated backChecked
      (by intro target same; have equal := Option.some.inj same; simpa [← equal] using exitStill.bound)
  exact ⟨afterGenerated, beforeBody.trans (bodyExtension.trans (backExtension.trans finalExtension)), afterChecked⟩

theorem generated_edge_jumpBack (env : LEnv) (depth : Nat) (exit header : BlockId) :
    GeneratedEdgeRun env (some ⟨depth, exit, .jump header⟩) (emitTerm (.br header [])) := by
  intro before result after run generated loop checked
  exact generated_edge_emitTerm_at (.br header []) env before after result run generated checked loop.2

theorem generated_edge_rangeBack (env : LEnv) (depth : Nat) (exit header : BlockId)
    (ty : IntTy) (counter : ValueId) :
    GeneratedEdgeRun env (some ⟨depth, exit, .next header ty counter⟩) (rangeBack ty counter header) := by
  intro before result after run generated loop checked
  obtain ⟨extension, afterChecked⟩ := edge_rangeBack_at ty counter header env before after result run checked loop.2.1 loop.2.2
  have dense := dense_rangeBack ty counter header env before result after run generated.dense generated.live
  have targets := generatedTargets_rangeBack ty counter header run generated.targets loop.2.1.bound
  exact ⟨⟨dense.1, dense.2.1, targets⟩, extension, afterChecked⟩

theorem generated_edge_lowerBreak (env : LEnv) (context : Option LoopCtx) (origin : OriginId) :
    GeneratedEdgeRun env context (lowerStmt context (.brk origin)) := by
  intro before result after run generated loop checked
  obtain ⟨extension, afterChecked⟩ := edge_lowerBreak_at context origin env before after result run checked loop
  exact ⟨generated.lowerStmt context (.brk origin) loop.targets run, extension, afterChecked⟩

theorem generated_edge_lowerContinue (env : LEnv) (context : Option LoopCtx) (origin : OriginId) :
    GeneratedEdgeRun env context (lowerStmt context (.cont origin)) := by
  intro before result after run generated loop checked
  obtain ⟨extension, afterChecked⟩ := edge_lowerContinue_at context origin env before after result run checked loop
  exact ⟨generated.lowerStmt context (.cont origin) loop.targets run, extension, afterChecked⟩

theorem generated_edge_lowerWhile_at (env : LEnv) (context : Option LoopCtx) (header : BlockId)
    {condition : B ValueId} {body : Nat → BlockId → B ValueId}
    (conditionEdges : GeneratedEdgeRun env context condition)
    (bodyEdges : ∀ depth exit, GeneratedEdgeRun env (some ⟨depth, exit, .jump header⟩) (body depth exit))
    (before after : LS) (result : Unit)
    (run : lowerWhile header condition body env before = (result, after))
    (generated : GeneratedBuilderState before) (loop : LoopEdgeArguments context before)
    (checked : BuilderEdgeArguments before) (headerEdge : EdgeArguments before header []) :
    GeneratedBuilderState after ∧ EdgeExtension before after ∧ BuilderEdgeArguments after := by
  obtain ⟨conditionValue, middle, conditionRun, tail⟩ := bind_eq.mp run
  obtain ⟨middleGenerated, middleExtension, middleChecked⟩ :=
    conditionEdges before conditionValue middle conditionRun generated loop checked
  cases current : middle.cur with
  | none =>
    rw [whenLive_none _ _ env current] at tail
    obtain ⟨_, rfl⟩ := Prod.mk.inj tail
    exact ⟨middleGenerated, middleExtension, middleChecked⟩
  | some block =>
    rw [whenLive_some _ _ env current] at tail
    obtain ⟨afterGenerated, finalExtension, afterChecked⟩ :=
      generated_edge_loopBody_at env context conditionValue (.jump header) bodyEdges
        (fun depth exit => generated_edge_jumpBack env depth exit header)
        middle after result tail middleGenerated (loop.extend middleExtension) middleChecked
        (by simp [current]) (headerEdge.extend middleExtension)
    exact ⟨afterGenerated, middleExtension.trans finalExtension, afterChecked⟩

theorem generated_edge_lowerRange_at (env : LEnv) (context : Option LoopCtx)
    (ty : IntTy) (counter bound : ValueId) (header : BlockId)
    {body : Nat → BlockId → B ValueId}
    (bodyEdges : ∀ depth exit, GeneratedEdgeRun env (some ⟨depth, exit, .next header ty counter⟩) (body depth exit))
    (before after : LS) (result : Unit)
    (run : lowerRange ty counter bound header body env before = (result, after))
    (generated : GeneratedBuilderState before) (loop : LoopEdgeArguments context before)
    (checked : BuilderEdgeArguments before) (current : before.cur.isSome = true)
    (frame : CounterHeader before header ty counter)
    (counterTyped : before.vals[counter]? = some (some (.data (.int ty)))) :
    GeneratedBuilderState after ∧ EdgeExtension before after ∧ BuilderEdgeArguments after := by
  obtain ⟨condition, middle, compareRun, tail⟩ := bind_eq.mp run
  obtain ⟨middleGenerated, middleExtension, middleChecked⟩ :=
    generated_edge_emitDef env context (.cmp .lt ty counter bound) before condition middle compareRun generated loop checked
  have sameCurrent : middle.cur = before.cur := by
    cases equal : before.cur with
    | none => rw [emitDef_none _ env equal] at compareRun; simpa only [Function.comp_apply, equal] using congrArg (LS.cur ∘ Prod.snd) compareRun.symm
    | some block => rw [emitDef_run _ env equal] at compareRun; simpa only [Function.comp_apply, equal] using congrArg (LS.cur ∘ Prod.snd) compareRun.symm
  obtain ⟨afterGenerated, finalExtension, afterChecked⟩ :=
    generated_edge_loopBody_at env context condition (.next header ty counter) bodyEdges
      (fun depth exit => generated_edge_rangeBack env depth exit header ty counter)
      middle after result tail middleGenerated (loop.extend middleExtension) middleChecked
      (by simpa only [sameCurrent] using current)
      ⟨frame.extend middleExtension, middleExtension.types _ _ counterTyped⟩
  exact ⟨afterGenerated, middleExtension.trans finalExtension, afterChecked⟩

theorem generated_edge_lowerEach_at (env : LEnv) (context : Option LoopCtx)
    (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) (header : BlockId) (counter : ValueId)
    {body : Nat → BlockId → B ValueId}
    (bodyEdges : ∀ depth exit, GeneratedEdgeRun env (some ⟨depth, exit, .next header .i64 counter⟩) (body depth exit))
    (before after : LS) (result : Unit)
    (run : lowerEach regrow owner sampled header counter body env before = (result, after))
    (generated : GeneratedBuilderState before) (loop : LoopEdgeArguments context before)
    (checked : BuilderEdgeArguments before) (current : before.cur.isSome = true)
    (frame : CounterHeader before header .i64 counter)
    (counterTyped : before.vals[counter]? = some (some (.data (.int .i64)))) :
    GeneratedBuilderState after ∧ EdgeExtension before after ∧ BuilderEdgeArguments after := by
  obtain ⟨bound, middle, lengthRun, tail⟩ := bind_eq.mp run
  obtain ⟨middleGenerated, middleExtension, middleChecked⟩ :=
    generated_edge_eachLen env context regrow owner sampled before bound middle lengthRun generated loop checked
  have sameCurrent : middle.cur = before.cur := by
    cases regrow
    · obtain ⟨_, rfl⟩ := pure_eq.mp lengthRun; rfl
    · simp only [eachLen, ite_true] at lengthRun
      cases equal : before.cur with
      | none => rw [emitDef_none _ env equal] at lengthRun
                simpa only [Function.comp_apply, equal] using congrArg (LS.cur ∘ Prod.snd) lengthRun.symm
      | some block => rw [emitDef_run _ env equal] at lengthRun
                      simpa only [Function.comp_apply, equal] using congrArg (LS.cur ∘ Prod.snd) lengthRun.symm
  obtain ⟨afterGenerated, finalExtension, afterChecked⟩ :=
    generated_edge_lowerRange_at env context .i64 counter bound header bodyEdges middle after result tail
      middleGenerated (loop.extend middleExtension) middleChecked
      (by simpa only [sameCurrent] using current)
      (frame.extend middleExtension) (middleExtension.types _ _ counterTyped)
  exact ⟨afterGenerated, middleExtension.trans finalExtension, afterChecked⟩

end Goose.Lower.Validation

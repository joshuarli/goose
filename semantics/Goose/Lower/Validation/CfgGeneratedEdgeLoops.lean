import Goose.Lower.Validation.CfgGeneratedEdgeShortCircuit

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

end Goose.Lower.Validation

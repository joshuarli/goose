import Goose.Lower.DemandGeneratedBlockValue

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive GeneratedBlockUnitInstruction (module : Core.Module) (access : AccessEnv) :
    Func → RetainedSsaMap → DemandSourceLabel → Pt → Inst → Prop
  | unit {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {bindings : List (SlotId × ValueId × OriginId)} {block : Core.Block}
      {required : RetainedSsaMap} {point : Pt}
      (occurrence : GeneratedDemandOccurrence module function le root path (.block loop bindings true block) before)
      (rows : GeneratedDemandRows module access occurrence required)
      (noValue : block.value = none)
      (atPoint : (demandBlockValueBefore le before loop bindings block).pp = some point)
      (extended : ExtT (lowerBlock loop bindings true block le before).2 function.blocks) :
      GeneratedBlockUnitInstruction module access function required ⟨path, .block, .exit⟩ point
        (.def (emitDef .constUnit le (demandBlockValueBefore le before loop bindings block)).1 .constUnit)

theorem GeneratedBlockUnitInstruction.instruction {module : Core.Module} {access : AccessEnv}
    {function : Func} {required : RetainedSsaMap} {label : DemandSourceLabel} {point : Pt} {instruction : Inst}
    (site : GeneratedBlockUnitInstruction module access function required label point instruction) :
    instAt function point = some instruction := by
  cases site with
  | @unit le root path before loop bindings block required point occurrence rows noValue atPoint extended =>
    have extension := generated_block_value_extended extended
    rw [noValue] at extension
    simp only [lowerBlockValue, ite_true] at extension
    have emitted : emitDef .constUnit le (demandBlockValueBefore le before loop bindings block) =
        ((emitDef .constUnit le (demandBlockValueBefore le before loop bindings block)).1,
         (emitDef .constUnit le (demandBlockValueBefore le before loop bindings block)).2) := rfl
    simpa only [instAt_eq] using (emitDef_facts emitted atPoint extension).2.2.2.2

theorem accepted_generated_block_unit_runtime_step {cfg : Cfg} {env : Env} {stmts : List Stmt}
    {state addressedState after : St} (source : StmtsSource cfg env stmts state)
    {fuel : Nat} (evaluated : execStmts fuel cfg env stmts state = .ok (.normal .unit) addressedState)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before start : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {block : Core.Block}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop bindings true block) before)
    (all : source.all = block.stmts) (scope : source.scope = block.scope) (value : source.value = block.value)
    (noValue : block.value = none)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required)
    {initial frame : GIR.Frame} {point : Pt}
    (post : Post cfg env cx start initial
      (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block) frame point [])
    (bounded : map.Bounded (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block).vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, addressedState⟩)
    (extended : ExtT (lowerBlock loop bindings true block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Evidence.RuntimeStep cx.cfg cx.fn point frame addressedState next nextFrame after) :
    DemandNode.block (.mk source.scope source.all source.value) = .block block ∧
    GeneratedBlockUnitInstruction cfg.mod source.rootsEnv.access cx.fn required ⟨source.path, .block, .exit⟩ point
      (.def (lowerBlockValue true block.value (lowerEnv cfg.mod env.vars results)
        (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block)).1 .constUnit) ∧
    map.Covers required ∧
    DemandFrameAt cfg env cx source.world source.typingAfter source.rootsEnv
      (blockSuffixFuture source.context source.all.length) map.values map.runs ⟨point, frame, addressedState⟩ ∧
    next = (point.1, point.2 + 1) ∧ after = addressedState ∧
    Post cfg env cx start initial
      (lowerBlockValue true block.value (lowerEnv cfg.mod env.vars results)
        (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block)).2
      nextFrame next [((lowerBlockValue true block.value (lowerEnv cfg.mod env.vars results)
        (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block)).1, .val .unit)] ∧
    DemandFrameAt cfg env cx source.world source.typingAfter source.rootsEnv
      (blockSuffixFuture source.context source.all.length) map.values map.runs ⟨next, nextFrame, after⟩ := by
  let le := lowerEnv cfg.mod env.vars results
  let current := demandBlockValueBefore le before loop bindings block
  let emitted := emitDef .constUnit le current
  have lowered : lowerBlockValue true block.value le current = emitted := by
    rw [noValue]
    rfl
  have site : GeneratedBlockUnitInstruction cfg.mod source.rootsEnv.access cx.fn required
      ⟨source.path, .block, .exit⟩ point (.def emitted.1 .constUnit) := .unit occurrence rows noValue post.pp extended
  obtain ⟨finalTyping, _, framed, normal⟩ := (source.result fuel (.normal .unit) evaluated).frame
  have finalEq := normal .unit rfl
  subst finalTyping
  have blockEq : DemandNode.block (.mk source.scope source.all source.value) = .block block := by
    rw [scope, all, value]
    cases block
    rfl
  refine ⟨blockEq, ?_, coverage, ⟨⟨_, post.pp, post.rel⟩, framed, realized⟩, ?_⟩
  · change GeneratedBlockUnitInstruction _ _ _ _ _ _ (.def (lowerBlockValue true block.value le current).1 .constUnit)
    rw [lowered]
    exact site
  cases step with
  | define instruction execution =>
    cases site.instruction.symm.trans instruction
    simp only [execOp, execPure, pure_apply, Res.ok.injEq] at execution
    rcases execution with ⟨rfl, rfl⟩
    have extension := generated_block_value_extended extended
    have unitExtended : ExtT emitted.2 cx.fn.blocks := by
      change ExtT (lowerBlockValue true block.value le current).2 _ at extension
      rw [lowered] at extension
      exact extension
    obtain ⟨finalPost, _⟩ := Post.def_leaf post (show emitDef .constUnit le current = (emitted.1, emitted.2) from rfl)
      unitExtended (.val .unit)
    have leafPost := (Post.def_leaf (Post.init post.rel post.pp)
      (show emitDef .constUnit le current = (emitted.1, emitted.2) from rfl) unitExtended (.val .unit)).1
    have carried := realized.retained leafPost.same bounded.1 bounded.2 RetainsAliases.refl
    refine ⟨rfl, rfl, ?_, ⟨⟨_, leafPost.pp, leafPost.rel⟩, framed, carried⟩⟩
    change Post cfg env cx start initial (lowerBlockValue true block.value le current).2 _ _
      [((lowerBlockValue true block.value le current).1, .val .unit)]
    rw [lowered]
    exact finalPost
  | effect instruction execution => cases site.instruction.symm.trans instruction
  | branch instruction read enter => cases site.instruction.symm.trans instruction
  | branchTrue instruction test read enter => cases site.instruction.symm.trans instruction
  | branchFalse instruction test read enter => cases site.instruction.symm.trans instruction

end Goose.Lower

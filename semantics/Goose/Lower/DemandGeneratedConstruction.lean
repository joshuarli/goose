import Goose.Lower.DemandGeneratedInstructions

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Lower

private theorem lowerView_snapshot_run (place : Place) (le : LEnv) (before : LS) :
    lowerView (.of place) le before =
      emitDef (.snapshot (match (generalizing := false) place with | .var _ | .global _ => .owner | _ => .borrowed)
        (lowerPlace place le before).1) le (lowerPlace place le before).2 := by
  cases place <;> simp only [lowerView, bind_run]

theorem generated_global_expression_extended (module : Core.Module) (global : Core.Global) :
    ExtT (lowerExpr global.init (lowerEnv module #[] [global.ty]) startLS).2 (lowerGlobal module global).init.blocks := by
  let le := lowerEnv module #[] [global.ty]
  let body := lowerExpr global.init le startLS
  have tail : ExtT (emitTerm (.ret [body.1] (some global.org)) le body.2).2 (lowerGlobal module global).init.blocks := by
    rw [lowerGlobal_blocks]
    exact extT_finish _
  exact tail.of_adv (adv_emitTerm (rfl : emitTerm (.ret [body.1] (some global.org)) le body.2 = _))

theorem generated_function_body_extended (module : Core.Module) (context : Context) (implementation : Impl) :
    ExtT (lowerBlock none (callPre implementation) false implementation.body
      (lowerEnv module implementation.vars implementation.results.toList) (callEntry implementation)).2
      (lowerContextAt module context implementation).blocks := by
  let le := lowerEnv module implementation.vars implementation.results.toList
  let body := lowerBlock none (callPre implementation) false implementation.body le (callEntry implementation)
  have tail : ExtT (bodyTail implementation le body.1 body.2) (lowerContextAt module context implementation).blocks := by
    rw [lowerContextAt_blocks, lowerImpl_call_blocks]
    exact extT_finish _
  exact tail.of_adv (advB_finishFunction implementation body.1 _ _ _ _ rfl)

theorem generated_read_load_extended {le : LEnv} {before : LS} {place : Place} {blocks : Array GIR.Block}
    (extended : ExtT (lowerExpr (.read place) le before).2 blocks) :
    ExtT (emitDef (.load (lowerPlace place le before).1) le (lowerPlace place le before).2).2 blocks := by
  let addressed := lowerPlace place le before
  let loaded := emitDef (.load addressed.1) le addressed.2
  have recorded : ExtT (recordReadValueRootRecipe loaded.1 place le loaded.2).2 blocks := by
    simpa only [lowerExpr_read_run] using extended
  exact recorded.of_adv (advB_recordReadValueRootRecipe loaded.1 place _ _ _ _ rfl)

theorem generated_read_place_extended {le : LEnv} {before : LS} {place : Place} {blocks : Array GIR.Block}
    (extended : ExtT (lowerExpr (.read place) le before).2 blocks) :
    ExtT (lowerPlace place le before).2 blocks :=
  (generated_read_load_extended extended).of_adv (adv_emitDef rfl)

theorem generated_index_expression_extended {le : LEnv} {before : LS} {view : View} {index : Expr}
    {origin : OriginId} {blocks : Array GIR.Block}
    (extended : ExtT (lowerPlace (.elem view index origin) le before).2 blocks) :
    ExtT (lowerExpr index le (lowerView view le before).2).2 blocks := by
  let sampled := lowerView view le before
  let indexed := lowerExpr index le sampled.2
  have checked : ExtT (emitDef (.indexChecked sampled.1 indexed.1 (some origin)) le indexed.2).2 blocks := by
    simpa only [lowerPlace, bind_run] using extended
  exact checked.of_adv (adv_emitDef rfl)

theorem generated_index_view_extended {le : LEnv} {before : LS} {view : View} {index : Expr}
    {origin : OriginId} {blocks : Array GIR.Block}
    (extended : ExtT (lowerPlace (.elem view index origin) le before).2 blocks) :
    ExtT (lowerView view le before).2 blocks :=
  (generated_index_expression_extended extended).of_adv (advB_lowerExpr index _ _ _ _ rfl)

theorem generated_view_place_extended {le : LEnv} {before : LS} {place : Place} {blocks : Array GIR.Block}
    (extended : ExtT (lowerView (.of place) le before).2 blocks) :
    ExtT (lowerPlace place le before).2 blocks := by
  rw [lowerView_snapshot_run] at extended
  exact extended.of_adv (adv_emitDef rfl)

theorem generated_clear_place_extended {le : LEnv} {before : LS} {loop : Option LoopCtx} {place : Place}
    {origin : OriginId} {blocks : Array GIR.Block}
    (extended : ExtT (lowerStmt loop (.clear place origin) le before).2 blocks) :
    ExtT (lowerPlace place le before).2 blocks := by
  have cleared : ExtT (emitEffect (.clear (lowerPlace place le before).1 (some origin)) le (lowerPlace place le before).2).2 blocks := by
    simpa only [lowerStmt, bind_run] using extended
  exact cleared.of_adv (adv_emitEffect rfl)

theorem generated_block_value_result (le : LEnv) (before : LS) (loop : Option LoopCtx)
    (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block) :
    (lowerBlock loop bindings want block le before).1 =
      (lowerBlockValue want block.value le (demandBlockValueBefore le before loop bindings block)).1 := by
  cases block
  simp only [lowerBlock, inScope, bind_run, pushScope_run, popScope_run, pure_run,
    demandBlockValueBefore, demandBlockStatementsBefore, Core.Block.scope, Core.Block.stmts, Core.Block.value]

theorem generated_block_leave_extended {le : LEnv} {before : LS} {loop : Option LoopCtx}
    {parameters : List (SlotId × ValueId × OriginId)} {want : Bool} {block : Core.Block} {blocks : Array GIR.Block}
    (extended : ExtT (lowerBlock loop parameters want block le before).2 blocks) :
    ExtT (emitEffect (.leave block.scope) le
      (lowerBlockValue want block.value le (demandBlockValueBefore le before loop parameters block)).2).2 blocks := by
  cases block with
  | mk scope statements value =>
    simp only [lowerBlock, inScope, bind_run, pushScope_run, popScope_run, pure_run] at extended
    simpa only [ExtT, demandBlockValueBefore, demandBlockStatementsBefore, Core.Block.scope, Core.Block.stmts, Core.Block.value] using extended

theorem generated_block_value_extended {le : LEnv} {before : LS} {loop : Option LoopCtx}
    {parameters : List (SlotId × ValueId × OriginId)} {want : Bool} {block : Core.Block} {blocks : Array GIR.Block}
    (extended : ExtT (lowerBlock loop parameters want block le before).2 blocks) :
    ExtT (lowerBlockValue want block.value le (demandBlockValueBefore le before loop parameters block)).2 blocks :=
  (generated_block_leave_extended extended).of_adv (adv_emitEffect rfl)

theorem generated_block_statements_extended {le : LEnv} {before : LS} {loop : Option LoopCtx}
    {parameters : List (SlotId × ValueId × OriginId)} {want : Bool} {block : Core.Block} {blocks : Array GIR.Block}
    (extended : ExtT (lowerBlock loop parameters want block le before).2 blocks) :
    ExtT (lowerStmts loop block.stmts le (demandBlockStatementsBefore le before parameters block)).2 blocks :=
  (generated_block_value_extended extended).of_adv (advB_lowerBlockValue want block.value _ _ _ _ rfl)

theorem generated_block_parameters_extended {le : LEnv} {before : LS} {loop : Option LoopCtx}
    {parameters : List (SlotId × ValueId × OriginId)} {want : Bool} {block : Core.Block} {blocks : Array GIR.Block}
    (extended : ExtT (lowerBlock loop parameters want block le before).2 blocks) :
    ExtT (demandBlockStatementsBefore le before parameters block) blocks :=
  (generated_block_statements_extended extended).of_adv (advB_lowerStmts loop block.stmts _ _ _ _ rfl)

theorem generated_block_enter_extended {le : LEnv} {before : LS} {loop : Option LoopCtx}
    {parameters : List (SlotId × ValueId × OriginId)} {want : Bool} {block : Core.Block} {blocks : Array GIR.Block}
    (extended : ExtT (lowerBlock loop parameters want block le before).2 blocks) :
    ExtT (emitEffect (.enter block.scope) le before).2 blocks := by
  have parametersExtended := generated_block_parameters_extended extended
  unfold demandBlockStatementsBefore at parametersExtended
  have enteredExtended := parametersExtended.of_adv (advB_initSlots parameters _ _ _ _ rfl)
  simpa only [ExtT] using enteredExtended

theorem lowerStmts_append_run (loop : Option LoopCtx) (first rest : List Stmt) (le : LEnv) (before : LS) :
    lowerStmts loop (first ++ rest) le before = lowerStmts loop rest le (lowerStmts loop first le before).2 := by
  induction first generalizing before with
  | nil => simp only [List.nil_append, lowerStmts, pure_run]
  | cons statement first induction =>
    cases current : before.cur with
    | none =>
      cases rest <;> simp only [List.cons_append, lowerStmts, bind_run, isLive_none current, Bool.false_eq_true, ite_false, pure_run]
    | some block =>
      simp only [List.cons_append, lowerStmts, bind_run, isLive_run current, ite_true]
      exact induction _

theorem generated_statements_head_extended {le : LEnv} {before : LS} {loop : Option LoopCtx}
    {statement : Stmt} {rest : List Stmt} {blocks : Array GIR.Block} {point : Pt}
    (atPoint : before.pp = some point)
    (extended : ExtT (lowerStmts loop (statement :: rest) le before).2 blocks) :
    ExtT (lowerStmt loop statement le before).2 blocks := by
  obtain ⟨block, current, _, _⟩ := LS.pp_some atPoint
  simp only [lowerStmts, bind_run, isLive_run current, ite_true] at extended
  exact extended.of_adv (advB_lowerStmts loop rest _ _ _ _ rfl)

theorem generated_block_statement_extended {le : LEnv} {before : LS} {loop : Option LoopCtx}
    {parameters : List (SlotId × ValueId × OriginId)} {want : Bool} {block : Core.Block}
    {index : Nat} {statement : Stmt} {blocks : Array GIR.Block} {point : Pt}
    (statementAt : block.stmts[index]? = some statement)
    (atPoint : (lowerStmts loop (block.stmts.take index) le
      (demandBlockStatementsBefore le before parameters block)).2.pp = some point)
    (extended : ExtT (lowerBlock loop parameters want block le before).2 blocks) :
    ExtT (lowerStmt loop statement le (lowerStmts loop (block.stmts.take index) le
      (demandBlockStatementsBefore le before parameters block)).2).2 blocks := by
  have statementsExtended := generated_block_statements_extended extended
  obtain ⟨bound, selected⟩ := List.getElem?_eq_some_iff.mp statementAt
  have split : block.stmts = block.stmts.take index ++ statement :: block.stmts.drop (index + 1) := by
    calc
      block.stmts = block.stmts.take index ++ block.stmts.drop index := (List.take_append_drop index block.stmts).symm
      _ = _ := by rw [List.drop_eq_getElem_cons bound, selected]
  rw [split, lowerStmts_append_run] at statementsExtended
  exact generated_statements_head_extended atPoint statementsExtended

theorem GeneratedDemandInstruction.literal_auto {module : Core.Module} {access : AccessEnv} {function : Func}
    {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS} {type : IntTy} {number : Int}
    {point : Pt} {required : RetainedSsaMap}
    (occurrence : GeneratedDemandOccurrence module function le root path (.expression (.lit type number)) before)
    (rows : GeneratedDemandRows module access occurrence required) (atPoint : before.pp = some point)
    (extended : ExtT (lowerExpr (.lit type number) le before).2 function.blocks) :
    GeneratedDemandInstruction module access function required ⟨path, .expression, .entry⟩ point
      (.def (lowerExpr (.lit type number) le before).1 (.constInt type number)) := by
  apply GeneratedDemandInstruction.literal occurrence rows atPoint
  have emitted : emitDef (.constInt type number) le before =
      ((emitDef (.constInt type number) le before).1, (emitDef (.constInt type number) le before).2) := rfl
  have extension : ExtT (emitDef (.constInt type number) le before).2 function.blocks := by
    simpa only [lowerExpr] using extended
  simpa only [lowerExpr, instAt_eq] using (emitDef_facts emitted atPoint extension).2.2.2.2

theorem GeneratedDemandInstruction.globalAddress_auto {module : Core.Module} {access : AccessEnv} {function : Func}
    {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS} {global : GlobalId}
    {point : Pt} {required : RetainedSsaMap}
    (occurrence : GeneratedDemandOccurrence module function le root path (.place (.global global)) before)
    (rows : GeneratedDemandRows module access occurrence required) (atPoint : before.pp = some point)
    (extended : ExtT (lowerPlace (.global global) le before).2 function.blocks) :
    GeneratedDemandInstruction module access function required ⟨path, .place, .entry⟩ point
      (.def (lowerPlace (.global global) le before).1 (.globalAddr global)) := by
  apply GeneratedDemandInstruction.globalAddress occurrence rows atPoint
  have emitted : emitDef (.globalAddr global) le before =
      ((emitDef (.globalAddr global) le before).1, (emitDef (.globalAddr global) le before).2) := rfl
  have extension : ExtT (emitDef (.globalAddr global) le before).2 function.blocks := by
    simpa only [lowerPlace] using extended
  simpa only [lowerPlace, instAt_eq] using (emitDef_facts emitted atPoint extension).2.2.2.2

theorem GeneratedDemandInstruction.slotAddress_auto {module : Core.Module} {access : AccessEnv} {function : Func}
    {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS} {slot : VarId}
    {point : Pt} {required : RetainedSsaMap}
    (occurrence : GeneratedDemandOccurrence module function le root path (.place (.var slot)) before)
    (rows : GeneratedDemandRows module access occurrence required) (atPoint : before.pp = some point)
    (extended : ExtT (lowerPlace (.var slot) le before).2 function.blocks) :
    GeneratedDemandInstruction module access function required ⟨path, .place, .entry⟩ point
      (.def (lowerPlace (.var slot) le before).1 (.slotAddr slot)) := by
  apply GeneratedDemandInstruction.slotAddress occurrence rows atPoint
  have emitted : emitDef (.slotAddr slot) le before =
      ((emitDef (.slotAddr slot) le before).1, (emitDef (.slotAddr slot) le before).2) := rfl
  have extension : ExtT (emitDef (.slotAddr slot) le before).2 function.blocks := by
    simpa only [lowerPlace] using extended
  simpa only [lowerPlace, instAt_eq] using (emitDef_facts emitted atPoint extension).2.2.2.2

theorem GeneratedDemandInstruction.snapshot_auto {module : Core.Module} {access : AccessEnv} {function : Func}
    {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS} {place : Place}
    {point : Pt} {required : RetainedSsaMap}
    (occurrence : GeneratedDemandOccurrence module function le root path (.view (.of place)) before)
    (rows : GeneratedDemandRows module access occurrence required)
    (atPoint : (lowerPlace place le before).2.pp = some point)
    (extended : ExtT (lowerView (.of place) le before).2 function.blocks) :
    GeneratedDemandInstruction module access function required ⟨path, .view, .exit⟩ point
      (.def (lowerView (.of place) le before).1
        (.snapshot (match (generalizing := false) place with | .var _ | .global _ => .owner | _ => .borrowed)
          (lowerPlace place le before).1)) := by
  apply GeneratedDemandInstruction.snapshot occurrence rows atPoint
  let operation := Op.snapshot (match (generalizing := false) place with | .var _ | .global _ => .owner | _ => .borrowed)
    (lowerPlace place le before).1
  have emitted : emitDef operation le (lowerPlace place le before).2 =
      ((emitDef operation le (lowerPlace place le before).2).1, (emitDef operation le (lowerPlace place le before).2).2) := rfl
  have extension : ExtT (emitDef operation le (lowerPlace place le before).2).2 function.blocks := by
    simpa only [operation, lowerView_snapshot_run] using extended
  have instruction := (emitDef_facts emitted atPoint extension).2.2.2.2
  cases place <;> simpa only [operation, lowerView_snapshot_run, instAt_eq] using instruction

theorem GeneratedDemandInstruction.indexChecked_auto {module : Core.Module} {access : AccessEnv} {function : Func}
    {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS} {view : View} {index : Expr} {origin : OriginId}
    {point : Pt} {required : RetainedSsaMap}
    (occurrence : GeneratedDemandOccurrence module function le root path (.place (.elem view index origin)) before)
    (rows : GeneratedDemandRows module access (.index occurrence) required)
    (atPoint : (lowerExpr index le (lowerView view le before).2).2.pp = some point)
    (extended : ExtT (lowerPlace (.elem view index origin) le before).2 function.blocks) :
    GeneratedDemandInstruction module access function required ⟨path ++ [1], .expression, .exit⟩ point
      (.def (lowerPlace (.elem view index origin) le before).1
        (.indexChecked (lowerView view le before).1 (lowerExpr index le (lowerView view le before).2).1 (some origin))) := by
  apply GeneratedDemandInstruction.indexChecked occurrence rows atPoint
  let indexRun := lowerExpr index le (lowerView view le before).2
  let operation := Op.indexChecked (lowerView view le before).1 indexRun.1 (some origin)
  have emitted : emitDef operation le indexRun.2 = ((emitDef operation le indexRun.2).1, (emitDef operation le indexRun.2).2) := rfl
  have extension : ExtT (emitDef operation le indexRun.2).2 function.blocks := by
    simpa only [operation, indexRun, lowerPlace, bind_run] using extended
  simpa only [operation, indexRun, lowerPlace, bind_run, instAt_eq] using (emitDef_facts emitted atPoint extension).2.2.2.2

theorem GeneratedDemandInstruction.load_auto {module : Core.Module} {access : AccessEnv} {function : Func}
    {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS} {place : Place}
    {point : Pt} {required : RetainedSsaMap}
    (occurrence : GeneratedDemandOccurrence module function le root path (.expression (.read place)) before)
    (rows : GeneratedDemandRows module access occurrence required)
    (atPoint : (lowerPlace place le before).2.pp = some point)
    (extended : ExtT (lowerExpr (.read place) le before).2 function.blocks) :
    GeneratedDemandInstruction module access function required ⟨path ++ [0], .place, .exit⟩ point
      (.def (lowerExpr (.read place) le before).1 (.load (lowerPlace place le before).1)) := by
  apply GeneratedDemandInstruction.load occurrence rows atPoint
  let addressed := lowerPlace place le before
  let loaded := emitDef (.load addressed.1) le addressed.2
  have emitted : emitDef (.load addressed.1) le addressed.2 = (loaded.1, loaded.2) := rfl
  have instruction := (emitDef_facts emitted atPoint (generated_read_load_extended extended)).2.2.2.2
  simpa only [lowerExpr_read_run, instAt_eq] using instruction


theorem GeneratedDemandInstruction.blockEnter_auto {module : Core.Module} {access : AccessEnv} {function : Func}
    {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS} {loop : Option LoopCtx}
    {parameters : List (SlotId × ValueId × OriginId)} {want : Bool} {block : Core.Block}
    {point : Pt} {required : RetainedSsaMap}
    (occurrence : GeneratedDemandOccurrence module function le root path (.block loop parameters want block) before)
    (rows : GeneratedDemandRows module access occurrence required) (atPoint : before.pp = some point)
    (extended : ExtT (lowerBlock loop parameters want block le before).2 function.blocks) :
    GeneratedDemandInstruction module access function required ⟨path, .block, .entry⟩ point (.eff (.enter block.scope)) := by
  apply GeneratedDemandInstruction.blockEnter occurrence rows atPoint
  have extension := generated_block_enter_extended extended
  simpa only [instAt_eq] using (emitEffect_facts (rfl : emitEffect (.enter block.scope) le before = _)
    atPoint extension).2.2.2

theorem GeneratedDemandInstruction.blockLeave_auto {module : Core.Module} {access : AccessEnv} {function : Func}
    {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS} {loop : Option LoopCtx}
    {parameters : List (SlotId × ValueId × OriginId)} {want : Bool} {block : Core.Block}
    {point : Pt} {required : RetainedSsaMap}
    (occurrence : GeneratedDemandOccurrence module function le root path (.block loop parameters want block) before)
    (rows : GeneratedDemandRows module access occurrence required)
    (atPoint : (lowerBlockValue want block.value le (demandBlockValueBefore le before loop parameters block)).2.pp = some point)
    (extended : ExtT (lowerBlock loop parameters want block le before).2 function.blocks) :
    GeneratedDemandInstruction module access function required (match (generalizing := false) block.value with
      | some _ => ⟨path ++ [block.stmts.length], .expression, .exit⟩
      | none => ⟨path, .block, .exit⟩) point (.eff (.leave block.scope)) := by
  apply GeneratedDemandInstruction.blockLeave occurrence rows atPoint
  simpa only [instAt_eq] using (emitEffect_facts (rfl : emitEffect (.leave block.scope) le
    (lowerBlockValue want block.value le (demandBlockValueBefore le before loop parameters block)).2 = _)
    atPoint (generated_block_leave_extended extended)).2.2.2

theorem GeneratedDemandInstruction.clear_auto {module : Core.Module} {access : AccessEnv} {function : Func}
    {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS} {loop : Option LoopCtx}
    {place : Place} {origin : OriginId} {point : Pt} {required : RetainedSsaMap}
    (occurrence : GeneratedDemandOccurrence module function le root path (.statement loop (.clear place origin)) before)
    (rows : GeneratedDemandRows module access occurrence required)
    (atPoint : (lowerPlace place le before).2.pp = some point)
    (extended : ExtT (lowerStmt loop (.clear place origin) le before).2 function.blocks) :
    GeneratedDemandInstruction module access function required ⟨path ++ [0], .place, .exit⟩ point
      (.eff (.clear (lowerPlace place le before).1 (some origin))) := by
  apply GeneratedDemandInstruction.clear occurrence rows atPoint
  let operation := Effect.clear (lowerPlace place le before).1 (some origin)
  have emitted : emitEffect operation le (lowerPlace place le before).2 =
      ((emitEffect operation le (lowerPlace place le before).2).1, (emitEffect operation le (lowerPlace place le before).2).2) := rfl
  have extension : ExtT (emitEffect operation le (lowerPlace place le before).2).2 function.blocks := by
    simpa only [operation, lowerStmt, bind_run] using extended
  simpa only [operation, instAt_eq] using (emitEffect_facts emitted atPoint extension).2.2.2

theorem GeneratedDemandInstruction.globalReturn_auto {module : Core.Module} {access : AccessEnv}
    {globalId : GlobalId} {global : Core.Global} {point : Pt} {required : RetainedSsaMap}
    (globalAt : module.globals[globalId]? = some global)
    (rows : GeneratedDemandRows module access (.globalRoot globalAt) required)
    (atPoint : (lowerExpr global.init (lowerEnv module #[] [global.ty]) startLS).2.pp = some point) :
    GeneratedDemandInstruction module access (lowerGlobal module global).init required ⟨[], .expression, .exit⟩ point
      (.term (.ret [(lowerExpr global.init (lowerEnv module #[] [global.ty]) startLS).1] (some global.org))) := by
  apply GeneratedDemandInstruction.globalReturn globalAt rows atPoint
  let le := lowerEnv module #[] [global.ty]
  let body := lowerExpr global.init le startLS
  let terminator := Term.ret [body.1] (some global.org)
  have emitted : emitTerm terminator le body.2 = ((emitTerm terminator le body.2).1, (emitTerm terminator le body.2).2) := rfl
  have extended : ExtT (emitTerm terminator le body.2).2 (lowerGlobal module global).init.blocks := by
    rw [lowerGlobal_blocks]
    exact extT_finish _
  simpa only [instAt_eq] using (emitTerm_facts emitted atPoint extended).2.2.2

end Goose.Lower

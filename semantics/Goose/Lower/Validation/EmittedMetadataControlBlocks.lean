import Goose.Lower.Validation.EmittedMetadataControlExpressions
import Goose.Lower.Validation.SourceStatementTypingBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem EmittedMetadata.initSlots {le : LEnv} {before : LS} (checked : EmittedMetadata le before)
    (pre : List (SlotId × ValueId × OriginId)) (preTyped : EmittedPreTyped le before pre) :
    EmittedMetadata le (Goose.Lower.initSlots pre le before).2 := by
  induction pre generalizing before with
  | nil => exact checked
  | cons binding rest ih =>
    obtain ⟨slot, value, origin⟩ := binding
    obtain ⟨descriptor, slotAt, valueAt⟩ := preTyped slot value origin (by simp)
    have first := checked.emitEffect (.slotInit slot value (some origin)) (fun _ => .slotInit slotAt valueAt)
    have restTyped : EmittedPreTyped le (Goose.Lower.emitEffect (.slotInit slot value (some origin)) le before).2 rest :=
      (show EmittedPreTyped le before rest from fun x id org member => preTyped x id org (List.mem_cons_of_mem _ member)).retained
        (types_emitEffect (.slotInit slot value (some origin)) le before _ _ rfl)
    exact ih first restTyped

theorem metadata_control_lowerBlock {le : LEnv} {before : LS}
    (builder : EmittedMetadata le before) (generated : GeneratedBuilderState before)
    (loop : Option LoopCtx) (loopBounds : LoopBuilderTargets loop before)
    (loopTypes : EmittedLoopTypes loop before) (pre : List (SlotId × ValueId × OriginId))
    (preTyped : EmittedPreTyped le before pre)
    (want : Bool) (scope : ScopeId) (stmts : List Stmt) (value : Option Expr)
    (stmtsChecked : ∀ before, EmittedMetadata le before → GeneratedBuilderState before →
      EmittedLoopTypes loop before → LoopBuilderTargets loop before →
      EmittedMetadata le (Goose.Lower.lowerStmts loop stmts le before).2 ∧
      GeneratedBuilderState (Goose.Lower.lowerStmts loop stmts le before).2)
    (valueChecked : ∀ before, EmittedMetadata le before → GeneratedBuilderState before →
      EmittedMetadata le (Goose.Lower.lowerBlockValue want value le before).2 ∧
      GeneratedBuilderState (Goose.Lower.lowerBlockValue want value le before).2) :
    let after := (Goose.Lower.lowerBlock loop pre want (.mk scope stmts value) le before).2
    EmittedMetadata le after ∧ GeneratedBuilderState after := by
  let entered := Goose.Lower.emitEffect (.enter scope) le before
  let pushed := Goose.Lower.pushScope scope le entered.2
  let initialized := Goose.Lower.initSlots pre le pushed.2
  let statements := Goose.Lower.lowerStmts loop stmts le initialized.2
  let output := Goose.Lower.lowerBlockValue want value le statements.2
  let left := Goose.Lower.emitEffect (.leave scope) le output.2
  have enteredBuilder := builder.emitEffect (.enter scope)
    (fun _ => .enter scope)
  have pushedBuilder := enteredBuilder.pushScope scope
  have initialPrefix := (EmittedAt.emitEffect le before (.enter scope)).prefix.trans
    (EmittedAt.pushScope le entered.2 scope).prefix
  have initializedBuilder := pushedBuilder.initSlots pre (preTyped.retained initialPrefix.typed)
  have initializedTypes := initialPrefix.typed.trans ((EmittedRun.initSlots pre le pushed.2).prefix.typed)
  have enteredGenerated := generated.emitEffect (.enter scope) (show emitEffect (.enter scope) le before = entered from rfl)
  have pushedGenerated : GeneratedBuilderState pushed.2 :=
    ⟨enteredGenerated.dense, enteredGenerated.live, enteredGenerated.targets⟩
  have initializedGenerated := pushedGenerated.initSlots pre (show initSlots pre le pushed.2 = initialized from rfl)
  have initializedGrowth : before.blocks.size ≤ initialized.2.blocks.size := by
    have enterGrowth : before.blocks.size ≤ entered.2.blocks.size := (advB_emitEffect (.enter scope) le before _ _ (show emitEffect (.enter scope) le before = entered from rfl)).ext.1
    have initGrowth : pushed.2.blocks.size ≤ initialized.2.blocks.size := (advB_initSlots pre le pushed.2 _ _ (show initSlots pre le pushed.2 = initialized from rfl)).ext.1
    have pushSize : pushed.2.blocks.size = entered.2.blocks.size := rfl
    nat_omega
  have statementsBuilder := stmtsChecked initialized.2 initializedBuilder initializedGenerated
    (loopTypes.retained initializedTypes) (loopBounds.mono initializedGrowth)
  have outputBuilder := valueChecked statements.2 statementsBuilder.1 statementsBuilder.2
  have leftBuilder := outputBuilder.1.emitEffect (.leave scope)
    (fun _ => .leave scope)
  have poppedBuilder := leftBuilder.popScope
  have leftGenerated := outputBuilder.2.emitEffect (.leave scope)
    (show emitEffect (.leave scope) le output.2 = left from rfl)
  have poppedGenerated : GeneratedBuilderState (popScope le left.2).2 :=
    ⟨leftGenerated.dense, leftGenerated.live, leftGenerated.targets⟩
  simpa only [Goose.Lower.lowerBlock, Goose.Lower.inScope, bind_run, pure_run,
    entered, pushed, initialized, statements, output, left] using And.intro poppedBuilder poppedGenerated

theorem EmittedMetadataAction.lowerStmt {le : LEnv} (loop : Option LoopCtx) (stmt : Stmt)
    (checked : EmittedMetadataRun le loop (Goose.Lower.lowerStmt loop stmt)) :
    EmittedMetadataAction le loop (Goose.Lower.lowerStmt loop stmt) :=
  ⟨checked, dense_lowerStmt loop stmt, advB_lowerStmt loop stmt,
    generatedTargets_lowerStmt loop stmt, types_lowerStmt loop stmt⟩

theorem EmittedMetadataAction.lowerStmts {le : LEnv} (loop : Option LoopCtx) (stmts : List Stmt)
    (checked : EmittedMetadataRun le loop (Goose.Lower.lowerStmts loop stmts)) :
    EmittedMetadataAction le loop (Goose.Lower.lowerStmts loop stmts) :=
  ⟨checked, dense_lowerStmts loop stmts, advB_lowerStmts loop stmts,
    generatedTargets_lowerStmts loop stmts, types_lowerStmts loop stmts⟩

theorem metadata_source_statements {results : List Ty} (scope : ScopeId) (stmts : List Stmt)
    (children : ∀ stmt ∈ stmts, ∀ env scope, EmittedMetadataSourceStatement env results scope stmt)
    {env output : Core.TEnv} {start finish : Nat}
    (resultTypes : EmittedMetadataResultTypes env results)
    (source : Core.tyStmts env scope stmts start = .ok (output, finish)) (loop : Option LoopCtx) :
    EmittedMetadataRun (lowerEnv env.mod env.vars results) loop (lowerStmts loop stmts) := by
  induction stmts generalizing env start with
  | nil => exact (EmittedMetadataAction.pure _ loop ()).metadata
  | cons stmt rest ih =>
    obtain ⟨middle, next, headTyped, tailTyped⟩ := tyStmts_cons_children source
    have tables := tyStmt_tables stmt headTyped
    have middleResults : EmittedMetadataResultTypes middle results := by
      intro impl selected
      apply resultTypes impl
      simpa only [tables.2.2] using selected
    have same : lowerEnv middle.mod middle.vars results = lowerEnv env.mod env.vars results := by
      rw [tables.1, tables.2.1]
    have head := children stmt (by simp) env scope resultTypes headTyped loop
    have tail := ih (fun child member => children child (List.mem_cons_of_mem _ member)) middleResults tailTyped
    rw [same] at tail
    unfold lowerStmts
    refine ((EmittedMetadataAction.isLive _ loop).bind fun active => ?_).metadata
    cases active
    · exact EmittedMetadataAction.pure _ loop ()
    · exact (EmittedMetadataAction.lowerStmt loop stmt head).bind fun _ =>
        EmittedMetadataAction.lowerStmts loop rest tail

theorem metadata_source_block_parts {results : List Ty} (scope : ScopeId)
    (stmts : List Stmt) (value : Option Expr)
    (stmtChildren : ∀ stmt ∈ stmts, ∀ env scope, EmittedMetadataSourceStatement env results scope stmt)
    (valueChild : ∀ expr, value = some expr → ∀ env, EmittedMetadataSourceExpression env results expr) :
    ∀ env, EmittedMetadataSourceBlock env results (.mk scope stmts value) := by
  intro env resultTypes sourcePre type start finish source loop pre want before result after generated loopBounds loopTypes preTyped run checked
  obtain ⟨_, declared, output, statementStart, valueStart, declaration, statements, finalValue⟩ :=
    tyBlock_checked_children source
  have declaredTables := declarePre_tables sourcePre declaration
  have outputTables := tyStmts_tables stmts statements
  have declaredResults : EmittedMetadataResultTypes declared results := by
    intro impl selected
    apply resultTypes impl
    simpa only [declaredTables.2.2] using selected
  have outputResults : EmittedMetadataResultTypes output results := by
    intro impl selected
    apply declaredResults impl
    simpa only [outputTables.2.2] using selected
  have sameDeclared : lowerEnv declared.mod declared.vars results = lowerEnv env.mod env.vars results := by
    rw [declaredTables.1, declaredTables.2.1]
  have sameOutput : lowerEnv output.mod output.vars results = lowerEnv env.mod env.vars results := by
    rw [outputTables.1, outputTables.2.1, sameDeclared]
  have statementTrace := metadata_source_statements scope stmts stmtChildren declaredResults statements loop
  rw [sameDeclared] at statementTrace
  have valueTrace : EmittedMetadataAction (lowerEnv env.mod env.vars results) none (lowerBlockValue want value) := by
    cases value with
    | none =>
      cases want
      · exact EmittedMetadataAction.pure _ none 0
      · exact EmittedMetadataAction.emitDef _ none .constUnit
    | some expr =>
      have child := EmittedMetadataAction.lowerExpr expr (valueChild expr rfl output outputResults finalValue)
      rw [sameOutput] at child
      exact child
  have lowered := metadata_control_lowerBlock checked generated loop loopBounds loopTypes pre preTyped want scope stmts value
    (fun state checked generated loopTypes loopBounds =>
      ⟨statementTrace state _ _ generated loopBounds loopTypes rfl checked,
        generated.lowerStmts loop stmts loopBounds rfl⟩)
    (fun state checked generated =>
      ⟨valueTrace.metadata state _ _ generated trivial trivial rfl checked,
        generated.lowerBlockValue want value rfl⟩)
  simpa only [run] using lowered.1

end Goose.Lower.Validation

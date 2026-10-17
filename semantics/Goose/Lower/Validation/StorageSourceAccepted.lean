import Goose.Lower.Validation.StorageSourceGenerated
import Goose.Lower.Validation.StorageSourceResize
import Goose.Lower.Validation.StorageSourceRebind
import Goose.Lower.Validation.StorageSourceTransfers
import Goose.Lower.Validation.StorageSourceShortCircuit
import Goose.Lower.Validation.StorageSourceBlocks
import Goose.Lower.Validation.StorageSourceEach
import Goose.Lower.Validation.StorageSourceEachFrame
import Goose.Lower.Validation.StorageSourceEachValue
import Goose.Lower.Validation.OperandEach
import Goose.Lower.Validation.StorageSourceSliceReference
import Goose.Lower.Validation.SourceStatementTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

attribute [local irreducible] StorageAt

set_option maxHeartbeats 1600000 in
mutual

theorem storage_lowerExpr (expr : Expr) {env : Core.TEnv} (sourceTypes : SourceReadableEnvironment env)
    {type : Ty} {start finish : Nat} (source : Core.tyExpr env expr start = .ok (type, finish))
    (results : List Ty) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerExpr expr) := by
  cases expr with
  | lit type value | bool value => exact StorageAt.emitDef _ (by intros; trivial)
  | read place =>
    apply storage_read_source (storageSourceOutputs env results) source
    · intro info first last childSource state current
      exact storage_lowerPlace place sourceTypes childSource results current
    · exact generated
  | push owner value origin =>
    apply storage_push_source (storageSourceOutputs env results) source
    · intro info first last childSource state current
      exact storage_lowerPlace owner sourceTypes childSource results current
    · intro childType first last childSource state current
      exact storage_lowerExpr value sourceTypes childSource results current
    · exact generated
  | pop owner origin =>
    apply storage_pop_source (storageSourceOutputs env results) source
    · intro info first last childSource state current
      exact storage_lowerPlace owner sourceTypes childSource results current
    · exact generated
  | ref mutability place =>
    obtain ⟨info, next, placeSource, _, _⟩ := tyExpr_ref_place source
    exact (storage_lowerPlace place sourceTypes placeSource results generated).bind (StorageAt.borrowTo _ _ _ _)
  | len view =>
    simp only [Core.tyExpr] at source
    obtain ⟨pair, next, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact (storage_lowerView view sourceTypes childSource results generated).bind (StorageAt.emitDef _ (by intros; trivial))
  | un operation child origin =>
    obtain ⟨first, last, integer, childSource, _, _⟩ := tyExpr_un_child source
    exact (storage_lowerExpr child sourceTypes childSource results generated).bind
      ((StorageAt.intTyOf _ _ _).bind (StorageAt.emitDef _ (by intros; trivial)))
  | not child =>
    obtain ⟨next, childSource, _⟩ := tyExpr_not_child source
    exact (storage_lowerExpr child sourceTypes childSource results generated).bind (StorageAt.emitDef _ (by intros; trivial))
  | bin operation left right origin =>
    obtain ⟨leftStart, leftFinish, rightStart, rightFinish, integer, leftSource, rightSource, _⟩ := tyExpr_bin_children source
    apply (storage_lowerExpr left sourceTypes leftSource results generated).bind
    apply (storage_lowerExpr right sourceTypes rightSource results
      (generated.lowerExpr left (env := lowerEnv env.mod env.vars results) rfl)).bind
    exact (StorageAt.intTyOf _ _ _).bind (StorageAt.emitDef _ (by intros; trivial))
  | cmp operation left right =>
    obtain ⟨leftType, rightType, leftFinish, rightFinish, leftSource, rightSource, _, _⟩ := tyExpr_comparison_children source
    apply (storage_lowerExpr left sourceTypes leftSource results generated).bind
    apply (storage_lowerExpr right sourceTypes rightSource results
      (generated.lowerExpr left (env := lowerEnv env.mod env.vars results) rfl)).bind
    apply (StorageAt.valTy _ _ _).bind
    split <;> exact StorageAt.emitDef _ (by intros; trivial)
  | conv kind target child origin =>
    obtain ⟨src, dst, childStart, childFinish, childSource, _, _, _⟩ := tyExpr_conversion_child source
    apply (storage_lowerExpr child sourceTypes childSource results generated).bind
    exact (StorageAt.intTyOf _ _ _).bind (StorageAt.emitDef _ (by intros; trivial))
  | and left right | or left right =>
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, rightSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    apply (storage_lowerExpr left sourceTypes leftSource results generated).bind
    apply StorageAt.shortCircuit_generated _ _ (generated.lowerExpr left (env := lowerEnv env.mod env.vars results) rfl)
    intro state current
    exact storage_lowerExpr right sourceTypes rightSource results current
  | slice mutability view lower upper origin =>
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨pair, _, viewSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, lowerSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, upperSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    apply (storage_lowerView view sourceTypes viewSource results generated).bind
    have viewGenerated := generated.lowerView view (env := lowerEnv env.mod env.vars results) rfl
    apply (storage_lowerBound lower sourceTypes lowerSource results viewGenerated).bind
    apply (storage_lowerBound upper sourceTypes upperSource results
      (viewGenerated.lowerBound lower (env := lowerEnv env.mod env.vars results) rfl)).bind
    exact StorageAt.emitDef _ (by intros; trivial)
  | arrLit arrayType children =>
    obtain ⟨_, element, childStart, childFinish, _, _, childrenSource⟩ := tyExpr_arrayLiteral_children source
    exact (storage_lowerExprsAs children sourceTypes childrenSource results generated).bind
      (StorageAt.emitDef _ (by intros; trivial))
  | structLit structType children =>
    obtain ⟨_, descriptor, definitionFinish, childStart, childFinish, _, childrenSource⟩ := tyExpr_structLiteral_children source
    exact (storage_lowerStructExprs children sourceTypes childrenSource results generated).bind
      (StorageAt.emitDef _ (by intros; trivial))
  | fill arrayType child =>
    obtain ⟨_, element, size, childStart, childFinish, _, childSource⟩ := tyExpr_fill_child source
    exact (storage_lowerExpr child sourceTypes childSource results generated).bind (StorageAt.emitDef _ (by intros; trivial))
  | call context arguments origin =>
    obtain ⟨ctx, callee, argsStart, argsFinish, resultStart, _, _, length, argsSource, _⟩ := tyExpr_call_tables source
    apply (storage_lowerArgs arguments callee.params.toList sourceTypes argsSource length results generated).bind
    apply (StorageAt.emitDef _ (by intros; trivial)).bind
    apply (StorageAt.read _ _).bind
    split
    · exact (StorageAt.emitTerm _ _ _).bind (StorageAt.pure _ _ _)
    · exact (StorageAt.pure _ _ _).bind (StorageAt.pure _ _ _)
  | blockE body =>
    exact storage_lowerBlock body sourceTypes.exprEnv source results none [] true generated trivial
  | ifE condition thenBody elseBody =>
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, conditionSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, thenSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, elseSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    apply (storage_lowerExpr condition sourceTypes conditionSource results generated).bind
    apply StorageAt.whenLive
    intro current live
    apply StorageAt.fork_actions_generated _
      (generated.lowerExpr condition (env := lowerEnv env.mod env.vars results) rfl) (loop := none) trivial
      (dense_lowerBlock none [] true thenBody) (generatedTargets_lowerBlock none [] true thenBody)
    · intro state current bounds
      exact storage_lowerBlock thenBody sourceTypes.exprEnv thenSource results none [] true current trivial
    · intro state current bounds
      exact storage_lowerBlock elseBody sourceTypes.exprEnv elseSource results none [] true current trivial
    · exact fun _ _ _ _ state => StorageAt.joinValue _ state _ _ _ _
termination_by sizeOf expr

theorem storage_lowerPlace (place : Place) {env : Core.TEnv} (sourceTypes : SourceReadableEnvironment env)
    {info : PlaceInfo} {start finish : Nat} (source : Core.tyPlace env place start = .ok (info, finish))
    (results : List Ty) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerPlace place) := by
  cases place with
  | var slot | global slot => exact StorageAt.emitDef _ (by intros; trivial)
  | field owner index =>
    simp only [Core.tyPlace] at source
    obtain ⟨_, _, ownerSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact (storage_lowerPlace owner sourceTypes ownerSource results generated).bind (StorageAt.emitDef _ (by intros; trivial))
  | elem view index origin =>
    simp only [Core.tyPlace] at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, viewSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, indexSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    apply (storage_lowerView view sourceTypes viewSource results generated).bind
    apply (storage_lowerExpr index sourceTypes indexSource results
      (generated.lowerView view (env := lowerEnv env.mod env.vars results) rfl)).bind
    exact StorageAt.emitDef _ (by intros; trivial)
  | deref expr =>
    simp only [Core.tyPlace] at source
    obtain ⟨_, _, valueSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    cases shortcut : Core.sliceRefTy env expr with
    | some type => exact storage_sliceRef_source (storageSourceOutputs env results) shortcut generated
    | none =>
      simp only [shortcut] at valueSource
      obtain ⟨_, _, childSource, _⟩ := (st_bind_ok _ _ _ _).mp valueSource
      exact storage_lowerExpr expr sourceTypes childSource results generated
termination_by sizeOf place

theorem storage_lowerView (view : View) {env : Core.TEnv} (sourceTypes : SourceReadableEnvironment env)
    {pair : Ty × Bool} {start finish : Nat} (source : Core.tyView env view start = .ok (pair, finish))
    (results : List Ty) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerView view) := by
  cases view with
  | of place =>
    simp only [Core.tyView] at source
    obtain ⟨_, _, placeSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact (storage_lowerPlace place sourceTypes placeSource results generated).bind (StorageAt.emitDef _ (by intros; trivial))
  | val expr =>
    simp only [Core.tyView] at source
    obtain ⟨_, _, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact (storage_lowerExpr expr sourceTypes childSource results generated).bind (StorageAt.emitDef _ (by intros; trivial))
termination_by sizeOf view

theorem storage_lowerBound (bound : Bound) {env : Core.TEnv} (sourceTypes : SourceReadableEnvironment env)
    {start finish : Nat} (source : Core.tyBound env bound start = .ok ((), finish))
    (results : List Ty) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerBound bound) := by
  cases bound with
  | omitted => exact StorageAt.pure _ _ _
  | expr child | fromEnd child =>
    simp only [Core.tyBound] at source
    obtain ⟨_, _, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact (storage_lowerExpr child sourceTypes childSource results generated).bind (StorageAt.pure _ _ _)
termination_by sizeOf bound

theorem storage_lowerExprsAs (expressions : List Expr) {env : Core.TEnv}
    (sourceTypes : SourceReadableEnvironment env) {element : Ty} {start finish : Nat}
    (source : Core.tyExprsAs env element expressions start = .ok ((), finish))
    (results : List Ty) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerExprs expressions) := by
  cases expressions with
  | nil => exact StorageAt.pure _ _ _
  | cons expression rest =>
    simp only [Core.tyExprsAs] at source
    obtain ⟨type, next, childSource, tail⟩ := (st_bind_ok _ _ _ _).mp source
    have tailSource : Core.tyExprsAs env element rest next = .ok ((), finish) := by
      by_cases equal : (type == element) = true
      · simpa [equal, pure, bind, StateT.pure, StateT.bind] using tail
      · simp [equal, chk] at tail
    apply (storage_lowerExpr expression sourceTypes childSource results generated).bind
    exact (storage_lowerExprsAs rest sourceTypes tailSource results
      (generated.lowerExpr expression (env := lowerEnv env.mod env.vars results) rfl)).bind (StorageAt.pure _ _ _)
termination_by sizeOf expressions

theorem storage_lowerStructExprs (expressions : List Expr) {env : Core.TEnv}
    (sourceTypes : SourceReadableEnvironment env) {types : List Ty} {start finish : Nat}
    (source : Core.tyStructExprs env types expressions start = .ok ((), finish))
    (results : List Ty) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerExprs expressions) := by
  cases expressions with
  | nil => exact StorageAt.pure _ _ _
  | cons expression rest =>
    cases types with
    | nil => simp [Core.tyStructExprs, chk] at source
    | cons expected types =>
      simp only [Core.tyStructExprs] at source
      obtain ⟨type, next, childSource, tail⟩ := (st_bind_ok _ _ _ _).mp source
      have tailSource : Core.tyStructExprs env types rest next = .ok ((), finish) := by
        by_cases equal : (type == expected) = true
        · simpa [equal, pure, bind, StateT.pure, StateT.bind] using tail
        · simp [equal, chk] at tail
      apply (storage_lowerExpr expression sourceTypes childSource results generated).bind
      exact (storage_lowerStructExprs rest sourceTypes tailSource results
        (generated.lowerExpr expression (env := lowerEnv env.mod env.vars results) rfl)).bind (StorageAt.pure _ _ _)
termination_by sizeOf expressions

theorem storage_lowerArgs (arguments : List Arg) (parameters : List Param) {env : Core.TEnv}
    (sourceTypes : SourceReadableEnvironment env) {callee : Core.Impl} {start finish : Nat}
    (source : Core.tyArgs env callee parameters arguments start = .ok ((), finish))
    (length : parameters.length = arguments.length)
    (results : List Ty) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerArgs arguments) := by
  cases arguments with
  | nil => exact StorageAt.pure _ _ _
  | cons argument rest =>
    cases parameters with
    | nil => simp at length
    | cons parameter parameters =>
      have tailLength : parameters.length = rest.length := by simpa using length
      cases row : callee.vars[parameter.var]? with
      | none =>
        cases argument <;> simp only [Core.tyArgs, row] at source
        all_goals inv at source
      | some localVar =>
        cases argument with
        | byVal expression =>
          simp only [Core.tyArgs, row] at source
          inv at source
          repeat' first
            | (guard_hyp source : _ ∧ _; obtain ⟨fact, source⟩ := source)
            | (guard_hyp source : ∃ _, _; obtain ⟨value, source⟩ := source)
          apply StorageAt.bind
          · exact storage_lowerExpr expression sourceTypes (by assumption) results generated
          · exact (storage_lowerArgs rest parameters sourceTypes (by assumption) tailLength results
              (generated.lowerArg (.byVal expression) (env := lowerEnv env.mod env.vars results) rfl)).bind (StorageAt.pure _ _ _)
        | byRef mutability place =>
          simp only [Core.tyArgs, row] at source
          inv at source
          repeat' first
            | (guard_hyp source : _ ∧ _; obtain ⟨fact, source⟩ := source)
            | (guard_hyp source : ∃ _, _; obtain ⟨value, source⟩ := source)
          have tailSource : ∃ next, Core.tyArgs env callee parameters rest next = .ok ((), finish) := by
            rcases source with ⟨_, _, _, tail⟩ | ⟨_, _, tail⟩
            all_goals exact ⟨_, tail⟩
          obtain ⟨next, tailSource⟩ := tailSource
          apply StorageAt.bind
          · exact (storage_lowerPlace place sourceTypes (by assumption) results generated).bind (StorageAt.borrowTo _ _ _ _)
          · exact (storage_lowerArgs rest parameters sourceTypes tailSource tailLength results
              (generated.lowerArg (.byRef mutability place) (env := lowerEnv env.mod env.vars results) rfl)).bind (StorageAt.pure _ _ _)
termination_by sizeOf arguments

theorem storage_lowerPrintArgs (arguments : List PrintArg) {env : Core.TEnv}
    (sourceTypes : SourceReadableEnvironment env) {start finish : Nat}
    (source : Core.tyPrintArgs env arguments start = .ok ((), finish))
    (results : List Ty) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerPrintArgs arguments) := by
  cases arguments with
  | nil => exact StorageAt.pure _ _ _
  | cons argument rest =>
    cases argument with
    | text text => exact (storage_lowerPrintArgs rest sourceTypes source results generated).bind (StorageAt.pure _ _ _)
    | expr expression =>
      simp only [Core.tyPrintArgs] at source
      obtain ⟨type, next, childSource, tail⟩ := (st_bind_ok _ _ _ _).mp source
      have tailSource : Core.tyPrintArgs env rest next = .ok ((), finish) := by
        cases type <;> simp only at tail
        all_goals first | exact tail | exact (rej_ok _ _ _ _).mp tail |>.elim
      apply (storage_lowerExpr expression sourceTypes childSource results generated).bind
      exact (storage_lowerPrintArgs rest sourceTypes tailSource results
        (generated.lowerExpr expression (env := lowerEnv env.mod env.vars results) rfl)).bind (StorageAt.pure _ _ _)
termination_by sizeOf arguments

theorem storage_lowerBlock (body : Core.Block) {env : Core.TEnv} (sourceTypes : SourceReadableEnvironment env)
    {sourcePre : List (VarId × Ty)} {type : Ty} {start finish : Nat}
    (source : Core.tyBlock env sourcePre body start = .ok (type, finish))
    (results : List Ty) (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool)
    {before : LS} (generated : GeneratedBuilderState before) (bounds : LoopBuilderTargets loop before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerBlock loop pre want body) := by
  cases body with
  | mk scope statements value =>
    obtain ⟨_, declared, output, statementStart, valueStart, declaration, statementsSource, valueSource⟩ := tyBlock_checked_children source
    have declaredTables := declarePre_tables sourcePre declaration
    have outputTables := tyStmts_tables statements statementsSource
    have declaredTypes := sourceTypes.tables declaredTables.1 declaredTables.2.1
    have outputTypes := declaredTypes.tables outputTables.1 outputTables.2.1
    have declaredEnv := declarePre_lowerEnv declaration results
    have outputEnv := (tyStmts_lowerEnv statementsSource results).trans declaredEnv
    apply StorageAt.block_generated loop pre want scope statements value generated bounds
    · intro state current targets
      simpa only [declaredEnv] using storage_lowerStmts statements declaredTypes statementsSource results loop current targets
    · intro state current
      cases value with
      | none => cases want <;> first | exact StorageAt.pure _ _ _ | exact StorageAt.emitDef _ (by intros; trivial)
      | some expression =>
        simpa only [outputEnv, lowerBlockValue] using storage_lowerExpr expression outputTypes valueSource results current
termination_by sizeOf body

theorem storage_lowerStmts (statements : List Stmt) {env output : Core.TEnv}
    (sourceTypes : SourceReadableEnvironment env) {scope start finish : Nat}
    (source : Core.tyStmts env scope statements start = .ok (output, finish))
    (results : List Ty) (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before)
    (bounds : LoopBuilderTargets loop before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerStmts loop statements) := by
  cases statements with
  | nil => exact StorageAt.pure _ _ _
  | cons statement rest =>
    obtain ⟨middle, next, headSource, tailSource⟩ := tyStmts_cons_children source
    have tables := tyStmt_tables statement headSource
    have middleTypes := sourceTypes.tables tables.1 tables.2.1
    have middleEnv : lowerEnv middle.mod middle.vars results = lowerEnv env.mod env.vars results := by rw [tables.1, tables.2.1]
    unfold lowerStmts
    apply (StorageAt.isLive _ _).bind
    split
    · apply (storage_lowerStmt statement sourceTypes headSource results loop generated bounds).bind
      have nextGenerated := generated.lowerStmt loop statement bounds (env := lowerEnv env.mod env.vars results) rfl
      have nextBounds := (generatedTargets_lowerStmt loop statement (lowerEnv env.mod env.vars results) before _ _ rfl generated.targets bounds).2
      simpa only [middleEnv] using storage_lowerStmts rest middleTypes tailSource results loop nextGenerated nextBounds
    · exact StorageAt.pure _ _ _
termination_by sizeOf statements

theorem storage_lowerStmt (statement : Stmt) {env output : Core.TEnv}
    (sourceTypes : SourceReadableEnvironment env) {scope start finish : Nat}
    (source : Core.tyStmt env scope statement start = .ok (output, finish))
    (results : List Ty) (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before)
    (bounds : LoopBuilderTargets loop before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerStmt loop statement) := by
  cases statement with
  | letS slot expr origin =>
    apply storage_let_source source
    · intro type first last childSource state current
      exact storage_lowerExpr expr sourceTypes childSource results current
    · exact generated
  | assign place expr origin =>
    apply storage_assign_source (storageSourceOutputs env results) source
    · intro info first last childSource state current
      exact storage_lowerPlace place sourceTypes childSource results current
    · intro type first last childSource state current
      exact storage_lowerExpr expr sourceTypes childSource results current
    · exact generated
  | assignOp operation place expr origin =>
    apply storage_assignOp_source (storageSourceOutputs env results) source
    · intro info first last childSource state current
      exact storage_lowerPlace place sourceTypes childSource results current
    · intro type first last childSource state current
      exact storage_lowerExpr expr sourceTypes childSource results current
    · exact generated
  | rebind slot expr origin =>
    apply storage_rebind_source source sourceTypes
    · intro type first last childSource state current
      exact storage_lowerExpr expr sourceTypes childSource results current
    · exact generated
  | expr expr origin =>
    apply storage_expr_source source
    · intro type first last childSource state current
      exact storage_lowerExpr expr sourceTypes childSource results current
    · exact generated
  | append owner view origin =>
    apply storage_append_source (storageSourceOutputs env results) source
    · intro info first last childSource state current
      exact storage_lowerPlace owner sourceTypes childSource results current
    · intro element writable first last childSource state current
      exact storage_lowerView view sourceTypes childSource results current
    · exact generated
  | popN owner count origin =>
    apply storage_popN_source (storageSourceOutputs env results) source
    · intro info first last childSource state current
      exact storage_lowerPlace owner sourceTypes childSource results current
    · intro type first last childSource state current
      exact storage_lowerExpr count sourceTypes childSource results current
    · exact generated
  | resize owner size fill origin =>
    apply storage_resize_source (storageSourceOutputs env results) source
    · intro info first last childSource state current
      exact storage_lowerPlace owner sourceTypes childSource results current
    · intro type first last childSource state current
      exact storage_lowerExpr size sourceTypes childSource results current
    · intro expression atFill type first last childSource state current
      cases atFill
      exact storage_lowerExpr expression sourceTypes childSource results current
    · exact generated
  | clear owner origin =>
    apply storage_clear_source (storageSourceOutputs env results) source
    · intro info first last childSource state current
      exact storage_lowerPlace owner sourceTypes childSource results current
    · exact generated
  | assignWhole owner expr origin =>
    apply storage_assignWhole_source (storageSourceOutputs env results) source
    · intro info first last childSource state current
      exact storage_lowerPlace owner sourceTypes childSource results current
    · intro type first last childSource state current
      exact storage_lowerExpr expr sourceTypes childSource results current
    · exact generated
  | ret value origin =>
    cases value with
    | none => exact StorageAt.return_none _ _ _ _
    | some expr =>
      apply storage_return_source source
      · intro type first last childSource state current
        exact storage_lowerExpr expr sourceTypes childSource results current
      · exact generated
  | brk origin => exact StorageAt.breakStmt _ _ _ _
  | cont origin => exact StorageAt.continueStmt _ _ _ _
  | abort message origin => exact StorageAt.emitTerm _ _ _
  | exit expr origin =>
    apply storage_exit_source source
    · intro type first last childSource state current
      exact storage_lowerExpr expr sourceTypes childSource results current
    · exact generated
  | assertS expr origin =>
    apply storage_assert_source source
    · intro type first last childSource state current
      exact storage_lowerExpr expr sourceTypes childSource results current
    · exact generated
  | print arguments origin =>
    exact (storage_lowerPrintArgs arguments sourceTypes (tyStmt_print_children source).1 results generated).bind
      (StorageAt.emitEffect _ (by intros; trivial))
  | ifS condition thenBody otherwise origin =>
    cases otherwise with
    | some elseBody =>
      obtain ⟨conditionFinish, thenType, thenFinish, conditionSource, thenSource, elseSource, _⟩ := tyStmt_if_children source
      let le := lowerEnv env.mod env.vars results
      let tested := lowerExpr condition le before
      have testedGenerated := generated.lowerExpr condition (show lowerExpr condition le before = tested from rfl)
      have testedBounds := bounds.mono
        ((dense_lowerExpr condition le before tested.1 tested.2 rfl generated.dense generated.live).2.2)
      apply (storage_lowerExpr condition sourceTypes conditionSource results generated).bind
      apply StorageAt.whenLive
      intro current live
      obtain ⟨elseType, childSource⟩ := elseSource
      apply StorageAt.fork_actions_generated _ testedGenerated testedBounds
        (dense_lowerBlock loop [] false thenBody) (generatedTargets_lowerBlock loop [] false thenBody)
      · intro state current targets
        exact storage_lowerBlock thenBody sourceTypes thenSource results loop [] false current targets
      · intro state current targets
        exact storage_lowerBlock elseBody sourceTypes childSource results loop [] false current targets
      · exact fun _ _ _ _ state => StorageAt.joinArms _ state _ _
    | none =>
      obtain ⟨conditionFinish, thenType, thenFinish, conditionSource, thenSource, elseSource, _⟩ := tyStmt_if_children source
      let le := lowerEnv env.mod env.vars results
      let tested := lowerExpr condition le before
      have testedGenerated := generated.lowerExpr condition (show lowerExpr condition le before = tested from rfl)
      have testedBounds := bounds.mono
        ((dense_lowerExpr condition le before tested.1 tested.2 rfl generated.dense generated.live).2.2)
      apply (storage_lowerExpr condition sourceTypes conditionSource results generated).bind
      apply StorageAt.whenLive
      intro current live
      let forked := fork tested.1 le tested.2
      let entered := setCur (some forked.1.1) le forked.2
      have forkedGenerated := testedGenerated.fork tested.1 (show fork tested.1 le tested.2 = forked from rfl)
      have ids : forked.1 = (tested.2.blocks.size, tested.2.blocks.size + 1) ∧
          forked.2.blocks.size = tested.2.blocks.size + 2 := fork_ids rfl
      have thenBound : forked.1.1 < forked.2.blocks.size := by simp only [ids.1, ids.2]; nat_omega
      have enteredGenerated := forkedGenerated.setCur (some forked.1.1)
        (by intro target same; cases same; exact thenBound)
        (show setCur _ le forked.2 = entered from rfl)
      have enteredBounds : LoopBuilderTargets loop entered.2 := testedBounds.mono (by change tested.2.blocks.size ≤ forked.2.blocks.size; rw [ids.2]; nat_omega)
      apply (StorageAt.fork _ _ _).bind
      apply (StorageAt.setCur _ _ _).bind
      exact (storage_lowerBlock thenBody sourceTypes thenSource results loop [] false enteredGenerated enteredBounds).bind
        ((StorageAt.emitTerm _ _ _).bind (StorageAt.setCur _ _ _))
  | «while» condition body origin =>
    obtain ⟨conditionFinish, bodyType, conditionSource, bodySource, _⟩ := tyStmt_while_children source
    apply StorageAt.header_generated (α := Unit)
      (tail := fun header _ => lowerWhile header (lowerExpr condition)
        (fun depth exit => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body)) [] [] generated
    intro header parameters state current headerBound
    let le := lowerEnv env.mod env.vars results
    let tested := lowerExpr condition le state
    have testedGenerated := current.lowerExpr condition (show lowerExpr condition le state = tested from rfl)
    have headerLater : header < tested.2.blocks.size := Nat.lt_of_lt_of_le headerBound
      ((dense_lowerExpr condition le state tested.1 tested.2 rfl current.dense current.live).2.2)
    apply StorageAt.lowerWhile_generated header
      (storage_lowerExpr condition sourceTypes conditionSource results current) testedGenerated
    intro depth exit bodyState bodyGenerated exitBound grows
    exact storage_lowerBlock body (sourceTypes.tables (after := { env with loops := env.loops + 1 }) rfl rfl) bodySource results
      (some ⟨depth, exit, .jump header⟩) [] false bodyGenerated
      ⟨exitBound, Nat.lt_of_lt_of_le headerLater grows⟩
  | forRange slot lower upper body origin =>
    obtain ⟨localVar, integer, lowerStart, lowerFinish, upperFinish, bodyType,
      _, lowerSource, upperSource, _, bodySource, _⟩ := tyStmt_forRange_children source
    let le := lowerEnv env.mod env.vars results
    let low := lowerExpr lower le before
    let high := lowerExpr upper le low.2
    let kind := intTyOf low.1 le high.2
    have lowGenerated := generated.lowerExpr lower (show lowerExpr lower le before = low from rfl)
    have highGenerated := lowGenerated.lowerExpr upper (show lowerExpr upper le low.2 = high from rfl)
    have kindGenerated := highGenerated.intTyOf low.1 (show intTyOf low.1 le high.2 = kind from rfl)
    apply (storage_lowerExpr lower sourceTypes lowerSource results generated).bind
    apply (storage_lowerExpr upper sourceTypes upperSource results lowGenerated).bind
    apply StorageAt.whenLive
    intro block live
    apply (StorageAt.intTyOf _ _ _).bind
    apply StorageAt.header_generated (α := Unit) (le := le) (before := kind.2)
      (tail := fun header parameters => lowerRange kind.1 (parameters.headD 0) high.1 header
        (fun depth exit => lowerBlock (some ⟨depth, exit, .next header kind.1 (parameters.headD 0)⟩)
          [(slot, parameters.headD 0, origin)] false body)) [.data (.int kind.1)] [low.1] kindGenerated
    intro header parameters state current headerBound
    apply StorageAt.lowerRange_generated _ _ _ _ current
    intro depth exit bodyState bodyGenerated exitBound grows
    have headerLater : header < bodyState.blocks.size := Nat.lt_of_lt_of_le headerBound
      (Nat.le_trans ((dense_emitDef (.cmp .lt kind.1 (parameters.headD 0) high.1)
        le state _ _ rfl current.dense current.live).2.2) grows)
    exact storage_lowerBlock body (sourceTypes.tables
      (after := { env with loops := env.loops + 1, visible := slot :: env.visible }) rfl rfl) bodySource results
      (some ⟨depth, exit, .next header kind.1 (parameters.headD 0)⟩)
      [(slot, parameters.headD 0, origin)] false bodyGenerated ⟨exitBound, headerLater⟩
  | forEach slot index view byReference body origin =>
    apply storage_forEach_source (storageSourceOutputs env results) sourceTypes source
    · intro element writable first last childSource state current
      exact storage_lowerView view sourceTypes childSource results current
    · intro type first last childSource childLoop pre state current childBounds
      exact storage_lowerBlock body (sourceTypes.tables
        (after := { env with loops := env.loops + 1, visible := slot :: index.toList ++ env.visible })
        rfl rfl) childSource results childLoop pre false current childBounds
    · exact generated

termination_by sizeOf statement

end

#print axioms storage_lowerExpr
#print axioms storage_lowerStmt
#print axioms storage_lowerBlock

end Goose.Lower.Validation

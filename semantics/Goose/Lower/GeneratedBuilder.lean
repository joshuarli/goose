import Goose.Lower.GeneratedTargetsSource
import Goose.Lower.Validation.DenseDefinitions

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Lower.Validation

structure GeneratedBuilderState (state : LS) : Prop where
  dense : state.DenseDefinitions
  live : LiveBound state
  targets : TargetsBounded state

theorem GeneratedBuilderState.of_runs {loop : Option LoopCtx} {action : B α}
    (denseRun : DenseRun action) (targetRun : GeneratedTargetRun loop action)
    {env : LEnv} {before after : LS} {result : α}
    (beforeGenerated : GeneratedBuilderState before)
    (loopBounds : LoopBuilderTargets loop before)
    (run : action env before = (result, after)) : GeneratedBuilderState after := by
  have dense := denseRun env before result after run beforeGenerated.dense beforeGenerated.live
  have targets := targetRun env before result after run beforeGenerated.targets loopBounds
  exact ⟨dense.1, dense.2.1, targets.1⟩

theorem GeneratedBuilderState.lowerExpr {before after : LS} (generated : GeneratedBuilderState before)
    (expr : Expr) {env : LEnv} {result : _}
    (run : lowerExpr expr env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_lowerExpr expr) (generatedTargets_lowerExpr none expr) trivial run

theorem GeneratedBuilderState.lowerExprs {before after : LS} (generated : GeneratedBuilderState before)
    (exprs : List Expr) {env : LEnv} {result : _}
    (run : lowerExprs exprs env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_lowerExprs exprs) (generatedTargets_lowerExprs none exprs) trivial run

theorem GeneratedBuilderState.lowerPlace {before after : LS} (generated : GeneratedBuilderState before)
    (place : Place) {env : LEnv} {result : _}
    (run : lowerPlace place env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_lowerPlace place) (generatedTargets_lowerPlace none place) trivial run

theorem GeneratedBuilderState.lowerView {before after : LS} (generated : GeneratedBuilderState before)
    (view : View) {env : LEnv} {result : _}
    (run : lowerView view env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_lowerView view) (generatedTargets_lowerView none view) trivial run

theorem GeneratedBuilderState.lowerBound {before after : LS} (generated : GeneratedBuilderState before)
    (bound : Bound) {env : LEnv} {result : _}
    (run : lowerBound bound env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_lowerBound bound) (generatedTargets_lowerBound none bound) trivial run

theorem GeneratedBuilderState.lowerArg {before after : LS} (generated : GeneratedBuilderState before)
    (arg : Arg) {env : LEnv} {result : _}
    (run : lowerArg arg env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_lowerArg arg) (generatedTargets_lowerArg none arg) trivial run

theorem GeneratedBuilderState.lowerArgs {before after : LS} (generated : GeneratedBuilderState before)
    (args : List Arg) {env : LEnv} {result : _}
    (run : lowerArgs args env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_lowerArgs args) (generatedTargets_lowerArgs none args) trivial run

theorem GeneratedBuilderState.lowerPrintArgs {before after : LS} (generated : GeneratedBuilderState before)
    (args : List PrintArg) {env : LEnv} {result : _}
    (run : lowerPrintArgs args env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_lowerPrintArgs args) (generatedTargets_lowerPrintArgs none args) trivial run

theorem GeneratedBuilderState.lowerEachSource {before after : LS} (generated : GeneratedBuilderState before)
    (view : View) {env : LEnv} {result : _}
    (run : lowerEachSource view env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_lowerEachSource view) (generatedTargets_lowerEachSource none view) trivial run

theorem GeneratedBuilderState.lowerBlockValue {before after : LS} (generated : GeneratedBuilderState before)
    (want : Bool) (value : Option Expr) {env : LEnv} {result : _}
    (run : lowerBlockValue want value env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_lowerBlockValue want value) (generatedTargets_lowerBlockValue none want value) trivial run

theorem GeneratedBuilderState.emitDef {before after : LS} (generated : GeneratedBuilderState before)
    (op : Op) {env : LEnv} {result : _}
    (run : emitDef op env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_emitDef op) (generatedTargets_emitDef none op) trivial run

theorem GeneratedBuilderState.emitEffect {before after : LS} (generated : GeneratedBuilderState before)
    (effect : Effect) {env : LEnv} {result : _}
    (run : emitEffect effect env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_emitEffect effect) (generatedTargets_emitEffect none effect) trivial run

theorem GeneratedBuilderState.newBlock {before after : LS} (generated : GeneratedBuilderState before)
    (types : List VTy) {env : LEnv} {result : _}
    (run : newBlock types env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_newBlock types) (generatedTargets_newBlock none types) trivial run

theorem GeneratedBuilderState.freezeTo {before after : LS} (generated : GeneratedBuilderState before)
    (mu : Mutability) (value : ValueId) {env : LEnv} {result : _}
    (run : freezeTo mu value env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_freezeTo mu value) (generatedTargets_freezeTo none mu value) trivial run

theorem GeneratedBuilderState.borrowTo {before after : LS} (generated : GeneratedBuilderState before)
    (mu : Mutability) (value : ValueId) {env : LEnv} {result : _}
    (run : borrowTo mu value env before = (result, after)) : GeneratedBuilderState after := by
  rcases borrowTo_cases run with freeze | owner
  · exact generated.freezeTo mu value freeze
  · exact generated.emitDef (.ownerBorrow value) owner

theorem GeneratedBuilderState.coerceTo {before after : LS} (generated : GeneratedBuilderState before)
    (ty : Ty) (value : ValueId) (origin : OriginId) {env : LEnv} {result : _}
    (run : coerceTo ty value origin env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_coerceTo ty value origin) (generatedTargets_coerceTo none ty value origin) trivial run

theorem GeneratedBuilderState.coerceSlot {before after : LS} (generated : GeneratedBuilderState before)
    (slot : SlotId) (value : ValueId) (origin : OriginId) {env : LEnv} {result : _}
    (run : coerceSlot slot value origin env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_coerceSlot slot value origin) (generatedTargets_coerceSlot none slot value origin) trivial run

theorem GeneratedBuilderState.coerceResult {before after : LS} (generated : GeneratedBuilderState before)
    (value : ValueId) (origin : OriginId) {env : LEnv} {result : _}
    (run : coerceResult value origin env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_coerceResult value origin) (generatedTargets_coerceResult none value origin) trivial run

theorem GeneratedBuilderState.initSlots {before after : LS} (generated : GeneratedBuilderState before)
    (slots : List (SlotId × ValueId × OriginId)) {env : LEnv} {result : _}
    (run : initSlots slots env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_initSlots slots) (generatedTargets_initSlots none slots) trivial run

theorem GeneratedBuilderState.leaveTo {before after : LS} (generated : GeneratedBuilderState before)
    (depth : Nat) {env : LEnv} {result : _}
    (run : leaveTo depth env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_leaveTo depth) (generatedTargets_leaveTo none depth) trivial run

theorem GeneratedBuilderState.emitTerm {before after : LS} (generated : GeneratedBuilderState before)
    (term : Term) (references : ∀ target ∈ term.successors, target < before.blocks.size)
    {env : LEnv} {result : Unit} (run : emitTerm term env before = (result, after)) :
    GeneratedBuilderState after := by
  have dense := dense_emitTerm term env before result after run generated.dense generated.live
  have targets := generated.targets.emitTerm term references env
  rw [run] at targets
  exact ⟨dense.1, dense.2.1, targets⟩

theorem GeneratedBuilderState.setCur {before after : LS} (generated : GeneratedBuilderState before)
    (block : Option BlockId) (bound : ∀ current, block = some current → current < before.blocks.size)
    {env : LEnv} {result : Unit} (run : setCur block env before = (result, after)) :
    GeneratedBuilderState after := by
  have dense := dense_setCur_at run generated.dense bound
  have targets := generatedTargets_setCur none block env before result after run generated.targets trivial
  exact ⟨dense.1, dense.2.1, targets.1⟩

theorem GeneratedBuilderState.fork {before after : LS} (generated : GeneratedBuilderState before)
    (condition : ValueId) {env : LEnv} {result : _}
    (run : fork condition env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_fork condition) (generatedTargets_fork none condition) trivial run

theorem GeneratedBuilderState.scFork {before after : LS} (generated : GeneratedBuilderState before)
    (isAnd : Bool) (value : ValueId) {env : LEnv} {result : _}
    (run : scFork isAnd value env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_scFork isAnd value) (generatedTargets_scFork none isAnd value) trivial run

theorem GeneratedBuilderState.joinValue {before after : LS} (generated : GeneratedBuilderState before)
    (yes : Option BlockId) (yesValue : ValueId) (no : Option BlockId) (noValue : ValueId) {env : LEnv} {result : _}
    (run : joinValue yes yesValue no noValue env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_joinValue yes yesValue no noValue) (generatedTargets_joinValue none yes no yesValue noValue) trivial run

theorem GeneratedBuilderState.joinArms {before after : LS} (generated : GeneratedBuilderState before)
    (yes no : Option BlockId) {env : LEnv} {result : _}
    (run : joinArms yes no env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_joinArms yes no) (generatedTargets_joinArms none yes no) trivial run

theorem GeneratedBuilderState.eachElemValue {before after : LS} (generated : GeneratedBuilderState before)
    (slot : VarId) (byRef : Bool) (value : ValueId) {env : LEnv} {result : _}
    (run : eachElemValue slot byRef value env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_eachElemValue slot byRef value) (generatedTargets_eachElemValue none slot byRef value) trivial run

theorem GeneratedBuilderState.regrowOf {before after : LS} (generated : GeneratedBuilderState before)
    (owner : Option ValueId) {env : LEnv} {result : _}
    (run : regrowOf owner env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_regrowOf owner) (generatedTargets_regrowOf none owner) trivial run

theorem GeneratedBuilderState.eachSampled {before after : LS} (generated : GeneratedBuilderState before)
    (regrow : Bool) (view : ValueId) {env : LEnv} {result : _}
    (run : eachSampled regrow view env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_eachSampled regrow view) (generatedTargets_eachSampled none regrow view) trivial run

theorem GeneratedBuilderState.eachLen {before after : LS} (generated : GeneratedBuilderState before)
    (regrow : Bool) (owner : Option ValueId) (view : ValueId) {env : LEnv} {result : _}
    (run : eachLen regrow owner view env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_eachLen regrow owner view) (generatedTargets_eachLen none regrow owner view) trivial run

theorem GeneratedBuilderState.valTy {before after : LS} (generated : GeneratedBuilderState before)
    (value : ValueId) {env : LEnv} {result : _}
    (run : valTy value env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_valTy value) (generatedTargets_valTy none value) trivial run

theorem GeneratedBuilderState.intTyOf {before after : LS} (generated : GeneratedBuilderState before)
    (value : ValueId) {env : LEnv} {result : _}
    (run : intTyOf value env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_intTyOf value) (generatedTargets_intTyOf none value) trivial run

theorem GeneratedBuilderState.lowerStmt {before after : LS} (generated : GeneratedBuilderState before)
    (loop : Option LoopCtx) (stmt : Stmt) (bounds : LoopBuilderTargets loop before) {env : LEnv} {result : _}
    (run : lowerStmt loop stmt env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_lowerStmt loop stmt) (generatedTargets_lowerStmt loop stmt) bounds run

theorem GeneratedBuilderState.lowerStmts {before after : LS} (generated : GeneratedBuilderState before)
    (loop : Option LoopCtx) (stmts : List Stmt) (bounds : LoopBuilderTargets loop before) {env : LEnv} {result : _}
    (run : lowerStmts loop stmts env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_lowerStmts loop stmts) (generatedTargets_lowerStmts loop stmts) bounds run

theorem GeneratedBuilderState.lowerBlock {before after : LS} (generated : GeneratedBuilderState before)
    (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block) (bounds : LoopBuilderTargets loop before) {env : LEnv} {result : _}
    (run : lowerBlock loop pre want block env before = (result, after)) : GeneratedBuilderState after :=
  generated.of_runs (dense_lowerBlock loop pre want block) (generatedTargets_lowerBlock loop pre want block) bounds run

theorem GeneratedBuilderState.initState : GeneratedBuilderState initState := by
  refine ⟨LS.denseDefinitions_initState, liveBound_initState, ?_⟩
  intro index body row
  simp [Goose.Lower.initState] at row

end Goose.Lower

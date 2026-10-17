import Goose.Lower.Validation.SnapshotContentsConstructors

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def SnapshotTraceRun (le : LEnv) (loop : Option LoopCtx) (action : B α) : Prop :=
  ∀ before result after, GeneratedBuilderState before → LoopBuilderFrames loop before →
    action le before = (result, after) → SnapshotSourceTrace le before.vals.size after after

theorem SnapshotTraceRun.pure {le : LEnv} {loop : Option LoopCtx} (value : α) :
    SnapshotTraceRun le loop (pure value) := by
  intro before result after generated _ run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact SnapshotSourceTrace.empty le before generated.dense

theorem SnapshotTraceRun.emitDef {le : LEnv} {loop : Option LoopCtx} (op : Op)
    (notSnapshot : ∀ mode owner, op ≠ .snapshot mode owner) :
    SnapshotTraceRun le loop (Goose.Lower.emitDef op) := by
  intro before result after generated _ run
  exact (SnapshotSourceTrace.empty le before generated.dense).emitDef generated run notSnapshot

theorem SnapshotTraceRun.same_values {le : LEnv} {loop : Option LoopCtx} {action : B α}
    (dense : DenseRun action) (advance : AdvB action) (typed : TypeRun action)
    (framed : GeneratedTargetFrameRun loop action)
    (same : ∀ before result after, action le before = (result, after) →
      after.vals.size = before.vals.size) : SnapshotTraceRun le loop action := by
  intro before result after generated frames run
  exact (SnapshotSourceTrace.empty le before generated.dense).extend_same_values run
    dense advance typed framed generated frames (same before result after run)

theorem SnapshotTraceRun.bind {le : LEnv} {loop : Option LoopCtx}
    {first : B α} {next : α → B β}
    (one : SnapshotTraceRun le loop first)
    (two : ∀ value, SnapshotTraceRun le loop (next value))
    (firstDense : DenseRun first) (firstAdvance : AdvB first)
    (firstTargets : GeneratedTargetRun loop first)
    (nextDense : ∀ value, DenseRun (next value))
    (nextAdvance : ∀ value, AdvB (next value))
    (nextTypes : ∀ value, TypeRun (next value))
    (nextFrames : ∀ value, GeneratedTargetFrameRun loop (next value)) :
    SnapshotTraceRun le loop (first >>= next) := by
  intro before result after generated frames run
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  have middleGenerated := generated.of_runs firstDense firstTargets frames.toTargets firstRun
  have middleFrames := frames.mono (firstAdvance le before value middle firstRun).ext
  have prior := (one before value middle generated frames firstRun).extend_framed nextRun
    (nextDense value) (nextAdvance value) (nextTypes value) (nextFrames value) middleGenerated middleFrames
  have suffix := two value middle result after middleGenerated middleFrames nextRun
  exact prior.seq suffix (firstAdvance le before value middle firstRun).vals middleGenerated.dense
    ((nextDense value) le middle result after nextRun middleGenerated.dense middleGenerated.live).1
    ((nextAdvance value) le middle result after nextRun).ext

theorem SnapshotTraceRun.continue {le : LEnv} {loop : Option LoopCtx} {action : B α}
    (source : SnapshotTraceRun le loop action)
    (dense : DenseRun action) (advance : AdvB action) (typed : TypeRun action)
    (framed : GeneratedTargetFrameRun loop action)
    {first : ValueId} {before after : LS} {result : α}
    (trace : SnapshotSourceTrace le first before before)
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before)
    (fresh : first ≤ before.vals.size) (run : action le before = (result, after)) :
    SnapshotSourceTrace le first after after := by
  have prior := trace.extend_framed run dense advance typed framed generated frames
  have suffix := source before result after generated frames run
  exact prior.seq suffix fresh generated.dense
    (dense le before result after run generated.dense generated.live).1
    (advance le before result after run).ext

theorem SnapshotSourceTrace.freezeTo {le : LEnv} {first owner result : ValueId}
    {before after : LS} {mu : Mutability}
    (trace : SnapshotSourceTrace le first before before)
    (generated : GeneratedBuilderState before)
    (run : Goose.Lower.freezeTo mu owner le before = (result, after)) :
    SnapshotSourceTrace le first after after := by
  rcases freezeTo_cases run with ⟨_, rfl⟩ | emitted
  · exact trace
  · exact trace.emitDef generated emitted (by intros; intro impossible; cases impossible)

theorem SnapshotSourceTrace.borrowTo {le : LEnv} {first owner result : ValueId}
    {before after : LS} {mu : Mutability}
    (trace : SnapshotSourceTrace le first before before)
    (generated : GeneratedBuilderState before)
    (run : Goose.Lower.borrowTo mu owner le before = (result, after)) :
    SnapshotSourceTrace le first after after := by
  rcases borrowTo_cases run with frozen | emitted
  · exact trace.freezeTo generated frozen
  · exact trace.emitDef generated emitted (by intros; intro impossible; cases impossible)

def SnapshotSourceExpression (env : Core.TEnv) (results : List Ty) (expr : Expr) : Prop :=
  ∀ {type : Ty} {start finish : Nat}, Core.tyExpr env expr start = .ok (type, finish) →
    SnapshotTraceRun (lowerEnv env.mod env.vars results) none (lowerExpr expr)

def SnapshotSourcePlace (env : Core.TEnv) (results : List Ty) (place : Place) : Prop :=
  ∀ {info : PlaceInfo} {start finish : Nat}, Core.tyPlace env place start = .ok (info, finish) →
    SnapshotTraceRun (lowerEnv env.mod env.vars results) none (lowerPlace place)

def SnapshotSourceView (env : Core.TEnv) (results : List Ty) (view : View) : Prop :=
  ∀ {element : Ty} {writable : Bool} {start finish : Nat},
    Core.tyView env view start = .ok ((element, writable), finish) →
    SnapshotTraceRun (lowerEnv env.mod env.vars results) none (lowerView view)

def SnapshotSourceStatement (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (stmt : Stmt) : Prop :=
  ∀ {output : Core.TEnv} {start finish : Nat}, Core.tyStmt env scope stmt start = .ok (output, finish) →
    ∀ loop, SnapshotTraceRun (lowerEnv env.mod env.vars results) loop (lowerStmt loop stmt)

def SnapshotSourceBlock (env : Core.TEnv) (results : List Ty) (body : Core.Block) : Prop :=
  ∀ {sourcePre : List (VarId × Ty)} {type : Ty} {start finish : Nat},
    Core.tyBlock env sourcePre body start = .ok (type, finish) →
    ∀ loop pre want, SnapshotTraceRun (lowerEnv env.mod env.vars results) loop (lowerBlock loop pre want body)

end Goose.Lower.Validation

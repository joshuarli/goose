import Goose.Lower.Validation.SnapshotContentsSourceLeavesActions
import Goose.Lower.Validation.SnapshotContentsBuilder
import Goose.Lower.Validation.EmittedTypingControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem SnapshotSourceTrace.recordValueRootRecipe {le : LEnv} {first : ValueId}
    {before after : LS} {value : ValueId} {scope : ScopeId} {result : Unit}
    (trace : SnapshotSourceTrace le first before before)
    (run : Goose.Lower.recordValueRootRecipe value scope le before = (result, after)) :
    SnapshotSourceTrace le first after after := by
  rw [recordValueRootRecipe_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  intro snapshot mode owner member bound
  obtain ⟨site, fresh, extension, typedPrefix, retention⟩ := trace snapshot mode owner member bound
  refine ⟨site, fresh, extension, typedPrefix, ?_⟩
  intro authorized witness
  have retained := retention authorized witness
  exact ⟨retained.closed, retained.noninteger, retained.ownerMember,
    retained.fresh, retained.beforeSnapshot⟩

def SnapshotFreeRun (action : B α) : Prop :=
  ∀ le before, NoNewSnapshots before (action le before).2

theorem SnapshotFreeRun.pure (value : α) : SnapshotFreeRun (pure value) :=
  fun _ before => .refl before

theorem SnapshotFreeRun.bind {first : B α} {next : α → B β}
    (one : SnapshotFreeRun first) (two : ∀ value, SnapshotFreeRun (next value)) :
    SnapshotFreeRun (first >>= next) :=
  fun le before => (one le before).trans (two (first le before).1 le (first le before).2)

theorem SnapshotFreeRun.setCur (current : Option BlockId) :
    SnapshotFreeRun (Goose.Lower.setCur current) := fun _ _ => .refl _

theorem SnapshotFreeRun.valTy (value : ValueId) : SnapshotFreeRun (Goose.Lower.valTy value) := by
  intro le before
  rw [valTy_run]
  exact .refl _

theorem SnapshotFreeRun.newBlock (types : List VTy) : SnapshotFreeRun (Goose.Lower.newBlock types) :=
  fun le before => NoNewSnapshots.newBlock (le := le) (before := before) (result := (Goose.Lower.newBlock types le before).1) types rfl

theorem SnapshotFreeRun.emitTerm (term : Term) : SnapshotFreeRun (Goose.Lower.emitTerm term) := by
  intro le before snapshot mode owner member
  cases live : before.cur with
  | none => simpa only [emitTerm_none term le live] using member
  | some block =>
    rw [emitTerm_run term le live] at member
    rcases emittedDef_appendInst member with old | fresh
    · exact old
    · cases fresh

theorem SnapshotFreeRun.patchTerm (block : BlockId) (term : Term) :
    SnapshotFreeRun (Goose.Lower.patchTerm block term) := by
  intro le before snapshot mode owner member
  rw [patchTerm_run] at member
  rcases emittedDef_appendInst member with old | fresh
  · exact old
  · cases fresh

theorem SnapshotFreeRun.patchBrs (target : BlockId) :
    ∀ incoming, SnapshotFreeRun (Goose.Lower.patchBrs target incoming)
  | [] => .pure ()
  | (_, _) :: rest => (SnapshotFreeRun.patchTerm _ _).bind fun _ => .patchBrs target rest

theorem SnapshotFreeRun.patchBrs0 (target : BlockId) :
    ∀ incoming, SnapshotFreeRun (Goose.Lower.patchBrs0 target incoming)
  | [] => .pure ()
  | _ :: rest => (SnapshotFreeRun.patchTerm _ _).bind fun _ => .patchBrs0 target rest

theorem SnapshotFreeRun.joinValue (yes no : Option BlockId) (left right : ValueId) :
    SnapshotFreeRun (Goose.Lower.joinValue yes left no right) := by
  unfold Goose.Lower.joinValue
  split
  · exact (SnapshotFreeRun.setCur _).bind fun _ => SnapshotFreeRun.pure _
  · exact (SnapshotFreeRun.valTy _).bind fun _ => (SnapshotFreeRun.newBlock _).bind fun _ =>
      (SnapshotFreeRun.patchBrs _ _).bind fun _ => (SnapshotFreeRun.setCur _).bind fun _ => SnapshotFreeRun.pure _

theorem SnapshotFreeRun.joinArms (yes no : Option BlockId) :
    SnapshotFreeRun (Goose.Lower.joinArms yes no) := by
  unfold Goose.Lower.joinArms
  split
  · exact SnapshotFreeRun.setCur _
  · exact (SnapshotFreeRun.newBlock _).bind fun _ =>
      (SnapshotFreeRun.patchBrs0 _ _).bind fun _ => SnapshotFreeRun.setCur _

theorem SnapshotFreeRun.fork (condition : ValueId) : SnapshotFreeRun (Goose.Lower.fork condition) := by
  unfold Goose.Lower.fork
  exact (SnapshotFreeRun.newBlock []).bind fun _ => (SnapshotFreeRun.newBlock []).bind fun _ =>
    (SnapshotFreeRun.emitTerm _).bind fun _ => .pure _

theorem SnapshotFreeRun.scFork (isAnd : Bool) (condition : ValueId) :
    SnapshotFreeRun (Goose.Lower.scFork isAnd condition) := by
  cases isAnd <;> unfold Goose.Lower.scFork
  all_goals exact (SnapshotFreeRun.newBlock []).bind fun _ => (SnapshotFreeRun.newBlock [.data .bool]).bind fun _ =>
    (SnapshotFreeRun.emitTerm _).bind fun _ => .pure _

theorem SnapshotTraceRun.of_free {le : LEnv} {loop : Option LoopCtx} {action : B α}
    (free : SnapshotFreeRun action) : SnapshotTraceRun le loop action := by
  intro before result after generated frames run snapshot mode owner member bound
  have prior := free le before snapshot mode owner (by simpa only [run] using member)
  exact (Nat.not_lt_of_ge bound (snapshot_definition_lt generated.dense prior)).elim

theorem SnapshotSourceTrace.extend_emitted_frame {le : LEnv} {loop : Option LoopCtx}
    {first : ValueId} {captured before after : LS} {result : α} {action : B α}
    (trace : SnapshotSourceTrace le first captured before)
    (run : action le before = (result, after)) (generated : GeneratedBuilderState before)
    (frames : LoopBuilderFrames loop before) (dense : DenseRun action)
    (emitted : EmittedRun action) (framed : GeneratedTargetFrameRun loop action) :
    SnapshotSourceTrace le first captured after := by
  have types := (emitted le before).prefix
  rw [run] at types
  have framing :=  framed before le before result after (.refl _) frames (.refl loop before) run
  have afterDense := (dense le before result after run generated.dense generated.live).1
  intro snapshot mode owner member bound
  obtain ⟨site, fresh, extension, prefixTypes, retention⟩ := trace snapshot mode owner member bound
  refine ⟨site, fresh, extension.trans framing.2, prefixTypes.trans types.typed, ?_⟩
  intro authorized witness
  exact (retention authorized witness).ext generated.dense afterDense framing.2 types.size types.typed frames framing.1

theorem SnapshotSourceTrace.joinValue {le : LEnv} {loop : Option LoopCtx}
    {first : ValueId} {before after : LS} {result left right : ValueId} {yes no : Option BlockId}
    (trace : SnapshotSourceTrace le first before before) (generated : GeneratedBuilderState before)
    (frames : LoopBuilderFrames loop before)
    (run : Goose.Lower.joinValue yes left no right le before = (result, after)) :
    SnapshotSourceTrace le first after after :=
  (trace.extend_emitted_frame run generated frames (dense_joinValue yes left no right)
    (EmittedRun.joinValue (yes, no) left right) (generatedTargetFrame_joinValue loop yes no left right)).recapture
      (by simpa only [run] using SnapshotFreeRun.joinValue yes no left right le before)

theorem SnapshotSourceTrace.joinArms {le : LEnv} {loop : Option LoopCtx}
    {first : ValueId} {before after : LS} {result : Unit} {yes no : Option BlockId}
    (trace : SnapshotSourceTrace le first before before) (generated : GeneratedBuilderState before)
    (frames : LoopBuilderFrames loop before)
    (run : Goose.Lower.joinArms yes no le before = (result, after)) :
    SnapshotSourceTrace le first after after :=
  (trace.extend_emitted_frame run generated frames (dense_joinArms yes no)
    (EmittedRun.joinArms yes no) (generatedTargetFrame_joinArms loop yes no)).recapture
      (by simpa only [run] using SnapshotFreeRun.joinArms yes no le before)

theorem SnapshotSourceAction.fork (le : LEnv) (loop : Option LoopCtx) (condition : ValueId) :
    SnapshotSourceAction le loop (Goose.Lower.fork condition) :=
  ⟨SnapshotTraceRun.of_free (.fork condition), dense_fork condition, advB_fork condition,
    generatedTargets_fork loop condition, types_fork condition, generatedTargetFrame_fork loop condition⟩

theorem SnapshotSourceAction.scFork (le : LEnv) (loop : Option LoopCtx) (isAnd : Bool) (condition : ValueId) :
    SnapshotSourceAction le loop (Goose.Lower.scFork isAnd condition) :=
  ⟨SnapshotTraceRun.of_free (.scFork isAnd condition), dense_scFork isAnd condition, advB_scFork isAnd condition,
    generatedTargets_scFork loop isAnd condition, types_scFork isAnd condition,
    generatedTargetFrame_scFork loop isAnd condition⟩

theorem SnapshotSourceAction.lowerBlock {le : LEnv} (loop : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (want : Bool) (body : Core.Block)
    (source : SnapshotTraceRun le loop (Goose.Lower.lowerBlock loop pre want body)) :
    SnapshotSourceAction le loop (Goose.Lower.lowerBlock loop pre want body) :=
  ⟨source, dense_lowerBlock loop pre want body, advB_lowerBlock loop pre want body,
    generatedTargets_lowerBlock loop pre want body, types_lowerBlock loop pre want body,
    generatedTargetFrame_lowerBlock loop pre want body⟩

theorem SnapshotSourceAction.lowerStmt {le : LEnv} (loop : Option LoopCtx) (stmt : Stmt)
    (source : SnapshotTraceRun le loop (Goose.Lower.lowerStmt loop stmt)) :
    SnapshotSourceAction le loop (Goose.Lower.lowerStmt loop stmt) :=
  ⟨source, dense_lowerStmt loop stmt, advB_lowerStmt loop stmt,
    generatedTargets_lowerStmt loop stmt, types_lowerStmt loop stmt,
    generatedTargetFrame_lowerStmt loop stmt⟩

theorem SnapshotSourceAction.lowerStmts {le : LEnv} (loop : Option LoopCtx) (stmts : List Stmt)
    (source : SnapshotTraceRun le loop (Goose.Lower.lowerStmts loop stmts)) :
    SnapshotSourceAction le loop (Goose.Lower.lowerStmts loop stmts) :=
  ⟨source, dense_lowerStmts loop stmts, advB_lowerStmts loop stmts,
    generatedTargets_lowerStmts loop stmts, types_lowerStmts loop stmts,
    generatedTargetFrame_lowerStmts loop stmts⟩

end Goose.Lower.Validation

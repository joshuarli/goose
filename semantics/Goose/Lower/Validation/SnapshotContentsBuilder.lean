import Goose.Lower.Validation.SnapshotContentsActions
import Goose.Lower.Validation.SnapshotContentsTraceControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem SnapshotSourceTrace.extend_no_new {α : Type} {action : B α} {le : LEnv}
    {first : ValueId} {before after : LS} {result : α} {loop : Option LoopCtx}
    (trace : SnapshotSourceTrace le first before before)
    (run : action le before = (result, after))
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (frameRun : GeneratedTargetFrameRun loop action)
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before)
    (unchanged : NoNewSnapshots before after) :
    SnapshotSourceTrace le first after after :=
  (trace.extend_framed run dense advances typed frameRun generated frames).recapture unchanged

theorem NoNewSnapshots.newBlock {le : LEnv} {before after : LS}
    {result : BlockId × List ValueId} (types : List VTy)
    (run : Goose.Lower.newBlock types le before = (result, after)) :
    NoNewSnapshots before after := by
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  intro snapshot mode owner member
  simpa [LS.insts] using member

theorem SnapshotSourceTrace.newBlock {le : LEnv} {first : ValueId} {before after : LS}
    {result : BlockId × List ValueId} (types : List VTy)
    (trace : SnapshotSourceTrace le first before before)
    (generated : GeneratedBuilderState before)
    (run : Goose.Lower.newBlock types le before = (result, after)) :
    SnapshotSourceTrace le first after after := by
  have advance : AdvB (Goose.Lower.newBlock types) := by
    intro env state result finish action
    rw [newBlock_run_general] at action
    obtain ⟨_, rfl⟩ := Prod.mk.inj action
    exact LS.Adv.newBlk state ⟨(paramIds types state.vals).zip types, #[]⟩
      (vs := pushParamTypes types state.vals) (by rw [array_size_pushParamTypes]; omega)
  exact trace.extend_no_new run (dense_newBlock types) advance
    (types_newBlock types) (generatedTargetFrame_newBlock none types) generated trivial
    (NoNewSnapshots.newBlock types run)

theorem SnapshotSourceTrace.emitTerm_before_full {le : LEnv} {first : ValueId}
    {before after : LS} {term : Term} {result : Unit}
    (trace : SnapshotSourceTrace le first before before)
    (generated : GeneratedBuilderState before)
    (run : Goose.Lower.emitTerm term le before = (result, after))
    (earlier : ∀ edge ∈ term.permissionEdges, ∀ destination,
      (permissionFunc le before).blocks[edge.1]? = some destination →
      ∀ parameter ∈ destination.params, parameter.1 < first) :
    SnapshotSourceTrace le first after after := by
  apply (trace.emitTerm_before generated run earlier).recapture
  apply NoNewSnapshots.of_same_values generated.dense
    (dense_emitTerm term le before result after run generated.dense generated.live).1
    (advB_emitTerm term le before result after run).ext
  cases live : before.cur with
  | none =>
    rw [emitTerm_none term le live] at run
    exact congrArg (fun pair => pair.2.vals.size) run.symm
  | some block =>
    rw [emitTerm_run term le live] at run
    exact congrArg (fun pair => pair.2.vals.size) run.symm

theorem SnapshotSourceTrace.setCur_full {le : LEnv} {first : ValueId}
    {before after : LS} {current : Option BlockId} {result : Unit}
    (trace : SnapshotSourceTrace le first before before)
    (run : Goose.Lower.setCur current le before = (result, after)) :
    SnapshotSourceTrace le first after after := by
  apply (trace.setCur run).recapture
  rw [setCur_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  intro snapshot mode owner member
  exact member

end Goose.Lower.Validation

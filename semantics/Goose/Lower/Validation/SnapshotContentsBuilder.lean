import Goose.Lower.Validation.SnapshotContentsActions
import Goose.Lower.Validation.SnapshotContentsTraceControl
import Goose.Lower.GeneratedTargetFramesControl

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

theorem SnapshotSourceTrace.fork {le : LEnv} {first : ValueId}
    {before after : LS} {condition : ValueId} {result : BlockId × BlockId}
    (trace : SnapshotSourceTrace le first before before)
    (generated : GeneratedBuilderState before)
    (run : Goose.Lower.fork condition le before = (result, after)) :
    SnapshotSourceTrace le first after after := by
  apply trace.extend_same_values run (dense_fork condition) (advB_fork condition)
    (types_fork condition) (generatedTargetFrame_fork none condition) generated trivial
  cases current : before.cur with
  | some block =>
    rw [fork_run condition le current] at run
    exact congrArg (fun pair => pair.2.vals.size) run.symm
  | none =>
    simp only [Goose.Lower.fork, bind_eq] at run
    obtain ⟨⟨tb, _⟩, one, oneRun, ⟨eb, _⟩, two, twoRun, _, closed, termRun, done⟩ := run
    rw [newBlock0_run] at oneRun twoRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj oneRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj twoRun
    rw [emitTerm_none _ le (show ({before with blocks := (before.blocks.push ⟨[], #[]⟩).push ⟨[], #[]⟩} : LS).cur = none from current)] at termRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj termRun
    obtain ⟨_, rfl⟩ := pure_eq.mp done
    rfl

theorem SnapshotSourceTrace.emitTerm_loop {le : LEnv} {first : ValueId}
    {before after : LS} {term : Term} {result : Unit} {loop : Option LoopCtx}
    (trace : SnapshotSourceTrace le first before before)
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before)
    (targets : ∀ target ∈ term.successors, LoopBuilderFrameTarget loop target)
    (run : Goose.Lower.emitTerm term le before = (result, after)) :
    SnapshotSourceTrace le first after after := by
  apply trace.extend_same_values run (dense_emitTerm term) (advB_emitTerm term)
    (types_emitTerm term) (generatedTargetFrame_emitTerm loop term
      (fun _ target member _ => targets target member)) generated frames
  cases current : before.cur with
  | none =>
    rw [emitTerm_none term le current] at run
    exact congrArg (fun pair => pair.2.vals.size) run.symm
  | some block =>
    rw [emitTerm_run term le current] at run
    exact congrArg (fun pair => pair.2.vals.size) run.symm

theorem SnapshotSourceTrace.emitTerm_integer {le : LEnv} {first : ValueId}
    {before after : LS} {term : Term} {result : Unit}
    (trace : SnapshotSourceTrace le first before before)
    (generated : GeneratedBuilderState before)
    (integers : ∀ edge ∈ term.permissionEdges, ∀ destination,
      (permissionFunc le before).blocks[edge.1]? = some destination →
      ∀ parameter ∈ destination.params, ∃ intTy, parameter.2 = .data (.int intTy))
    (run : Goose.Lower.emitTerm term le before = (result, after)) :
    SnapshotSourceTrace le first after after := by
  have retained : SnapshotSourceTrace le first before after := by
    intro snapshot mode owner member bound
    obtain ⟨site, fresh, extension, types, retention⟩ := trace snapshot mode owner member bound
    refine ⟨site, fresh, extension.trans (advB_emitTerm term le before result after run).ext,
      types.trans (types_emitTerm term le before result after run), retention.trans ?_⟩
    intro authorized witness
    apply witness.emitTerm generated.dense generated.live run
    intro edge edgeMember destination row entry belongs allowed
    have parameterMember := (List.of_mem_zip belongs).1
    obtain ⟨intTy, typed⟩ := integers edge edgeMember destination row entry.1 parameterMember
    exact (witness.noninteger destination
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? row)) entry.1 parameterMember allowed intTy typed).elim
  apply retained.recapture
  apply NoNewSnapshots.of_same_values generated.dense
    (dense_emitTerm term le before result after run generated.dense generated.live).1
    (advB_emitTerm term le before result after run).ext
  cases current : before.cur with
  | none =>
    rw [emitTerm_none term le current] at run
    exact congrArg (fun pair => pair.2.vals.size) run.symm
  | some block =>
    rw [emitTerm_run term le current] at run
    exact congrArg (fun pair => pair.2.vals.size) run.symm

end Goose.Lower.Validation

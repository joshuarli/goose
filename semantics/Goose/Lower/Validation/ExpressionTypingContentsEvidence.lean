import Goose.Lower.Validation.ExpressionTypingGraphTargets

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def ContentsEvidence (le : LEnv) (state : LS) (value : ValueId) : Prop :=
  ∃ authorized,
    ContentsClosed (le.globals.map (·.2)) le.mod.structs (permissionFunc le state) state.vals authorized ∧
    NonIntegerParameters (permissionFunc le state) authorized ∧ authorized value

theorem ContentsEvidence.contentsWritable {le : LEnv} {state : LS} {value : ValueId}
    (evidence : ContentsEvidence le state value) : (tyEnv le state).contentsWritable value = some true := by
  obtain ⟨authorized, closed, _, permitted⟩ := evidence
  exact closed.tyEnv_contents permitted

theorem ContentsEvidence.ext {le : LEnv} {before after : LS} {value : ValueId} {loop : Option LoopCtx}
    (evidence : ContentsEvidence le before value)
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (grows : before.vals.size ≤ after.vals.size)
    (types : TypePrefix before after) (frames : LoopBuilderFrames loop before)
    (framed : TermEdgesFramed loop before after) : ContentsEvidence le after value := by
  obtain ⟨authorized, closed, noninteger, permitted⟩ := evidence
  refine ⟨authorized, closed.ext beforeDense afterDense extension grows types frames framed noninteger, ?_, permitted⟩
  apply noninteger.ext beforeDense afterDense extension
  intro candidate member
  simpa only [permissionFunc_numValues beforeDense le] using closed.bounded candidate member

theorem ContentsEvidence.of_run {α : Type} {action : B α} {le : LEnv} {before after : LS}
    {value : ValueId} {result : α} {loop : Option LoopCtx}
    (evidence : ContentsEvidence le before value) (run : action le before = (result, after))
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (beforeDense : before.DenseDefinitions) (bounded : LiveBound before)
    (frames : LoopBuilderFrames loop before) (framed : TermEdgesFramed loop before after) :
    ContentsEvidence le after value := by
  have afterDense := (dense le before result after run beforeDense bounded).1
  have advanced := advances le before result after run
  exact evidence.ext beforeDense afterDense advanced.ext advanced.vals
    (typed le before result after run) frames framed

theorem contentsEvidence_fresh_definition {le : LEnv} {before after : LS} {value : ValueId} {op : Op}
    {current : BlockId} (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef op le before = (value, after))
    (operation : ContentsOperation (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals (fun candidate => candidate = value) value op) :
    ContentsEvidence le after value :=
  ⟨_, contentsClosed_fresh_definition checked bounded live run operation,
    nonIntegerParameters_fresh_definition checked live run, rfl⟩

theorem ContentsEvidence.emitDef_dependency {le : LEnv} {before after : LS}
    {owner value : ValueId} {op : Op} {current : BlockId}
    (evidence : ContentsEvidence le before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef op le before = (value, after))
    (operation : ∀ authorized, authorized owner →
      ContentsOperation (le.globals.map (·.2)) le.mod.structs
        (permissionFunc le after) after.vals authorized value op) :
    ContentsEvidence le after value := by
  obtain ⟨authorized, closed, noninteger, permitted⟩ := evidence
  refine ⟨fun candidate => authorized candidate ∨ candidate = value, ?_, ?_, Or.inr rfl⟩
  · exact closed.emitDef_extend checked bounded live run (operation _ (Or.inl permitted))
  · exact (noninteger.emitDef_preserve live run).union
      (nonIntegerParameters_fresh_definition checked live run)

theorem contentsEvidence_slot {le : LEnv} {before after : LS} {value : ValueId} {slot : SlotId}
    {descriptor : Slot} {current : BlockId} (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (row : le.slots[slot]? = some descriptor)
    (run : emitDef (.slotAddr slot) le before = (value, after)) :
    ContentsEvidence le after value := contentsEvidence_fresh_definition checked bounded live run ⟨descriptor, row⟩

theorem contentsEvidence_global {le : LEnv} {before after : LS} {value : ValueId} {global : GlobalId}
    {ty : Ty} {kind : VarKind} {current : BlockId} (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (row : le.globals[global]? = some (ty, kind))
    (run : emitDef (.globalAddr global) le before = (value, after)) :
    ContentsEvidence le after value := by
  apply contentsEvidence_fresh_definition checked bounded live run
  exact ⟨kind, by simp [Array.getElem?_map, row]⟩

theorem ContentsEvidence.snapshot {le : LEnv} {before after : LS}
    {owner value : ValueId} {mode : SnapshotMode} {current : BlockId}
    (evidence : ContentsEvidence le before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : emitDef (.snapshot mode owner) le before = (value, after)) :
    ContentsEvidence le after value :=
  evidence.emitDef_dependency checked bounded live run (fun _ permitted => permitted)

theorem ContentsEvidence.indexChecked {le : LEnv} {before after : LS}
    {owner value index : ValueId} {origin : Option OriginId} {current : BlockId}
    (evidence : ContentsEvidence le before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : emitDef (.indexChecked owner index origin) le before = (value, after)) :
    ContentsEvidence le after value :=
  evidence.emitDef_dependency checked bounded live run (fun _ permitted => permitted)

#print axioms ContentsEvidence.emitDef_dependency
#print axioms ContentsEvidence.contentsWritable

end Goose.Lower.Validation

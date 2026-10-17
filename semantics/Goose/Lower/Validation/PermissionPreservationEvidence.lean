import Goose.Lower.Validation.PermissionPreservationGraph

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def WritableEvidence (le : LEnv) (state : LS) (value : ValueId) : Prop :=
  ∃ writable contents,
    WritableClosed (le.globals.map (·.2)) le.mod.structs (permissionFunc le state) state.vals writable contents ∧
    ContentsClosed (le.globals.map (·.2)) le.mod.structs (permissionFunc le state) state.vals contents ∧
    NonIntegerParameters (permissionFunc le state) writable ∧
    NonIntegerParameters (permissionFunc le state) contents ∧ writable value

theorem WritableEvidence.permission {le : LEnv} {state : LS} {value : ValueId}
    (evidence : WritableEvidence le state value) :
    (permissionsAt ((permissionFunc le state).permissionsFromTables
      (le.globals.map (·.2)) le.mod.structs state.vals) value).1 = true := by
  obtain ⟨writable, contents, bindings, elements, _, _, permitted⟩ := evidence
  exact bindings.permissions elements value permitted

theorem WritableEvidence.ext {le : LEnv} {before after : LS} {value : ValueId} {loop : Option LoopCtx}
    (evidence : WritableEvidence le before value)
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (grows : before.vals.size ≤ after.vals.size)
    (types : TypePrefix before after) (frames : LoopBuilderFrames loop before)
    (framed : TermEdgesFramed loop before after) : WritableEvidence le after value := by
  obtain ⟨writable, contents, bindings, elements, bindingParameters, contentParameters, permitted⟩ := evidence
  refine ⟨writable, contents,
    bindings.ext beforeDense afterDense extension grows types frames framed bindingParameters,
    elements.ext beforeDense afterDense extension grows types frames framed contentParameters, ?_, ?_, permitted⟩
  · apply bindingParameters.ext beforeDense afterDense extension
    intro candidate member
    simpa only [permissionFunc_numValues beforeDense le] using bindings.bounded candidate member
  · apply contentParameters.ext beforeDense afterDense extension
    intro candidate member
    simpa only [permissionFunc_numValues beforeDense le] using elements.bounded candidate member

theorem WritableEvidence.of_run {α : Type} {action : B α} {le : LEnv} {before after : LS}
    {value : ValueId} {result : α} {loop : Option LoopCtx}
    (evidence : WritableEvidence le before value) (run : action le before = (result, after))
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (beforeDense : before.DenseDefinitions) (bounded : LiveBound before)
    (frames : LoopBuilderFrames loop before) (framed : TermEdgesFramed loop before after) :
    WritableEvidence le after value := by
  have afterDense := (dense le before result after run beforeDense bounded).1
  have advanced := advances le before result after run
  exact evidence.ext beforeDense afterDense advanced.ext advanced.vals
    (typed le before result after run) frames framed

theorem writableEvidence_fresh_definition {le : LEnv} {before after : LS} {value : ValueId} {op : Op}
    {current : BlockId} {contents : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef op le before = (value, after))
    (elements : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals contents)
    (parameters : NonIntegerParameters (permissionFunc le after) contents)
    (operation : WritableOperation (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals contents value op) :
    WritableEvidence le after value :=
  ⟨_, contents, writableClosed_fresh_definition checked bounded live run operation, elements,
    nonIntegerParameters_fresh_definition checked live run, parameters, rfl⟩

theorem writableEvidence_slot {le : LEnv} {before after : LS} {value : ValueId} {slot : SlotId}
    {descriptor : Slot} {current : BlockId} (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (row : le.slots[slot]? = some descriptor)
    (mutable : descriptor.kind = .mutable) (run : emitDef (.slotAddr slot) le before = (value, after)) :
    WritableEvidence le after value :=
  writableEvidence_fresh_definition checked bounded live run
    (ContentsClosed.empty _ _ _ _) (NonIntegerParameters.empty _) ⟨descriptor, row, mutable⟩

theorem writableEvidence_global {le : LEnv} {before after : LS} {value : ValueId} {global : GlobalId}
    {ty : Ty} {current : BlockId} (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (row : le.globals[global]? = some (ty, .mutable))
    (run : emitDef (.globalAddr global) le before = (value, after)) :
    WritableEvidence le after value := by
  apply writableEvidence_fresh_definition checked bounded live run
    (ContentsClosed.empty _ _ _ _) (NonIntegerParameters.empty _)
  simp only [WritableOperation, Array.getElem?_map, row, Option.map_some]

#print axioms WritableEvidence.permission
#print axioms WritableEvidence.of_run
#print axioms writableEvidence_slot
#print axioms writableEvidence_global

end Goose.Lower.Validation

import Goose.Lower.Validation.PermissionPreservationEvidence
import Goose.Lower.Validation.ExpressionTypingContentsEvidence

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ContentsEvidence.emitDef_binding_dependency {le : LEnv} {before after : LS}
    {owner value : ValueId} {op : Op} {current : BlockId}
    (evidence : ContentsEvidence le before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef op le before = (value, after))
    (operation : ∀ contents, contents owner →
      WritableOperation (le.globals.map (·.2)) le.mod.structs
        (permissionFunc le after) after.vals contents value op) :
    WritableEvidence le after value := by
  obtain ⟨contents, elements, parameters, permitted⟩ := evidence
  exact writableEvidence_fresh_definition checked bounded live run
    (elements.emitDef_preserve checked bounded live run) (parameters.emitDef_preserve live run)
    (operation contents permitted)

theorem ContentsEvidence.snapshot_binding {le : LEnv} {before after : LS}
    {owner value : ValueId} {mode : SnapshotMode} {current : BlockId}
    (evidence : ContentsEvidence le before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : emitDef (.snapshot mode owner) le before = (value, after)) :
    WritableEvidence le after value :=
  evidence.emitDef_binding_dependency checked bounded live run (fun _ permitted => permitted)

theorem ContentsEvidence.indexChecked_binding {le : LEnv} {before after : LS}
    {owner value index : ValueId} {origin : Option OriginId} {current : BlockId}
    (evidence : ContentsEvidence le before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : emitDef (.indexChecked owner index origin) le before = (value, after)) :
    WritableEvidence le after value :=
  evidence.emitDef_binding_dependency checked bounded live run (fun _ permitted => permitted)

theorem ContentsEvidence.fieldAddr_binding {le : LEnv} {before after : LS}
    {owner value index id : Nat} {fields : TyList} {mu : Mutability} {descriptor : StructDef}
    {field : StructField} {current : BlockId}
    (evidence : ContentsEvidence le before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (typed : before.vals[owner]? = some (some (.data (.ref mu (.structT id fields)))))
    (descriptorRow : le.mod.structs[id]? = some descriptor)
    (fieldRow : descriptor.fields[index]? = some field) (writable : field.binding = .mutable)
    (run : emitDef (.fieldAddr owner index) le before = (value, after)) :
    WritableEvidence le after value := by
  apply evidence.emitDef_binding_dependency checked bounded live run
  intro contents permitted
  exact ⟨permitted, mu, id, fields, descriptor, field,
    types_emitDef _ le before value after run owner _ typed, descriptorRow, fieldRow, writable⟩

#print axioms ContentsEvidence.emitDef_binding_dependency
#print axioms ContentsEvidence.indexChecked_binding
#print axioms ContentsEvidence.fieldAddr_binding

end Goose.Lower.Validation

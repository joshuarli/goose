import Goose.Lower.Validation.PermissionPreservationFresh

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem freshWritableEvidence_slot {le : LEnv} {before after : LS} {value : ValueId} {slot : SlotId}
    {descriptor : Slot} {current : BlockId} (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (row : le.slots[slot]? = some descriptor)
    (mutable : descriptor.kind = .mutable) (run : emitDef (.slotAddr slot) le before = (value, after)) :
    FreshWritableEvidence le before.vals.size after value := by
  apply freshWritableEvidence_definition checked bounded live run
    (ContentsClosed.empty _ _ _ _) (NonIntegerParameters.empty _)
    (by simp) (Nat.le_refl _)
  exact ⟨descriptor, row, mutable⟩

theorem freshWritableEvidence_global {le : LEnv} {before after : LS} {value : ValueId} {global : GlobalId}
    {ty : Ty} {current : BlockId} (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (row : le.globals[global]? = some (ty, .mutable))
    (run : emitDef (.globalAddr global) le before = (value, after)) :
    FreshWritableEvidence le before.vals.size after value := by
  apply freshWritableEvidence_definition checked bounded live run
    (ContentsClosed.empty _ _ _ _) (NonIntegerParameters.empty _)
    (by simp) (Nat.le_refl _)
  simp only [WritableOperation, Array.getElem?_map, row, Option.map_some]

theorem freshWritableEvidence_load {le : LEnv} {before after : LS}
    {owner value : ValueId} {referent : Ty} {current : BlockId}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef (.load owner) le before = (value, after))
    (typed : after.vals[value]? = some (some (.data (.ref .mutable referent)))) :
    FreshWritableEvidence le before.vals.size after value := by
  apply freshWritableEvidence_definition checked bounded live run
    (ContentsClosed.empty _ _ _ _) (NonIntegerParameters.empty _)
    (by simp) (Nat.le_refl _)
  simp only [WritableOperation, typedPermissions, typed]
  rfl

theorem freshWritableEvidence_call {le : LEnv} {before after : LS}
    {callee : FnId} {args : List ValueId} {origin : Option OriginId}
    {value : ValueId} {referent : Ty} {current : BlockId}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : emitDef (.call callee args origin) le before = (value, after))
    (typed : after.vals[value]? = some (some (.data (.ref .mutable referent)))) :
    FreshWritableEvidence le before.vals.size after value := by
  apply freshWritableEvidence_definition checked bounded live run
    (ContentsClosed.empty _ _ _ _) (NonIntegerParameters.empty _)
    (by simp) (Nat.le_refl _)
  simp only [WritableOperation, typedPermissions, typed]
  rfl

theorem freshWritableEvidence_push {le : LEnv} {before after : LS}
    {owner stored value : ValueId} {referent : Ty} {origin : Option OriginId} {current : BlockId}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : emitDef (.push owner stored origin) le before = (value, after))
    (typed : after.vals[value]? = some (some (.data (.ref .mutable referent)))) :
    FreshWritableEvidence le before.vals.size after value := by
  apply freshWritableEvidence_definition checked bounded live run
    (ContentsClosed.empty _ _ _ _) (NonIntegerParameters.empty _)
    (by simp) (Nat.le_refl _)
  simp only [WritableOperation, typedPermissions, typed]
  rfl

theorem freshWritableEvidence_pop {le : LEnv} {before after : LS}
    {owner value : ValueId} {referent : Ty} {origin : Option OriginId} {current : BlockId}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : emitDef (.pop owner origin) le before = (value, after))
    (typed : after.vals[value]? = some (some (.data (.ref .mutable referent)))) :
    FreshWritableEvidence le before.vals.size after value := by
  apply freshWritableEvidence_definition checked bounded live run
    (ContentsClosed.empty _ _ _ _) (NonIntegerParameters.empty _)
    (by simp) (Nat.le_refl _)
  simp only [WritableOperation, typedPermissions, typed]
  rfl

theorem FreshContentsEvidence.snapshot_binding {le : LEnv} {first : Nat} {before after : LS}
    {owner value : ValueId} {mode : SnapshotMode} {current : BlockId}
    (evidence : FreshContentsEvidence le first before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : emitDef (.snapshot mode owner) le before = (value, after)) :
    FreshWritableEvidence le first after value :=
  evidence.emitDef_binding_dependency checked bounded live run (fun _ permitted => permitted)

theorem FreshContentsEvidence.indexChecked_binding {le : LEnv} {first : Nat} {before after : LS}
    {owner value index : ValueId} {origin : Option OriginId} {current : BlockId}
    (evidence : FreshContentsEvidence le first before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : emitDef (.indexChecked owner index origin) le before = (value, after)) :
    FreshWritableEvidence le first after value :=
  evidence.emitDef_binding_dependency checked bounded live run (fun _ permitted => permitted)

theorem FreshContentsEvidence.fieldAddr_binding {le : LEnv} {first : Nat} {before after : LS}
    {owner value index id : Nat} {fields : TyList} {mu : Mutability} {descriptor : StructDef}
    {field : StructField} {current : BlockId}
    (evidence : FreshContentsEvidence le first before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (typed : before.vals[owner]? = some (some (.data (.ref mu (.structT id fields)))))
    (descriptorRow : le.mod.structs[id]? = some descriptor)
    (fieldRow : descriptor.fields[index]? = some field) (writable : field.binding = .mutable)
    (run : emitDef (.fieldAddr owner index) le before = (value, after)) :
    FreshWritableEvidence le first after value := by
  apply evidence.emitDef_binding_dependency checked bounded live run
  intro contents permitted
  exact ⟨permitted, mu, id, fields, descriptor, field,
    types_emitDef _ le before value after run owner _ typed, descriptorRow, fieldRow, writable⟩

#print axioms freshWritableEvidence_slot
#print axioms freshWritableEvidence_load
#print axioms freshWritableEvidence_call
#print axioms freshWritableEvidence_push
#print axioms freshWritableEvidence_pop
#print axioms FreshContentsEvidence.fieldAddr_binding

end Goose.Lower.Validation

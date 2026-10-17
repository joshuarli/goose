import Goose.Lower.Validation.ValueTypeReconstructionPermissionGraph

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure PermissionGraphExtension (before after : Func) : Prop where
  slots : before.slots = after.slots
  blocks : ∀ (index : BlockId) (block : GIR.Block), before.blocks[index]? = some block →
    ∃ next : GIR.Block, after.blocks[index]? = some next ∧ next.params = block.params ∧
      ∀ inst ∈ block.insts, inst ∈ next.insts
  operands : ∀ block ∈ before.blocks.toList, ∀ value op, .def value op ∈ block.insts →
    ∀ operand ∈ op.uses, operand < before.numValues
  arguments : ∀ block ∈ before.blocks.toList, ∀ term, .term term ∈ block.insts →
    ∀ edge ∈ term.permissionEdges, ∀ argument ∈ edge.2, argument < before.numValues

private theorem ContentsOperation.restrict
    {globalKinds : Array VarKind} {structs : Array StructDef} {before after : Func}
    {oldTypes newTypes : Array (Option VTy)} {authorized : ValueId → Prop}
    (slots : before.slots = after.slots)
    (prefixTypes : ∀ v, v < before.numValues → oldTypes[v]? = newTypes[v]?)
    {value : ValueId} {op : Op} (bound : value < before.numValues)
    (operands : ∀ v ∈ op.uses, v < before.numValues)
    (operation : ContentsOperation globalKinds structs after newTypes authorized value op) :
    ContentsOperation globalKinds structs before oldTypes
      (fun v => authorized v ∧ v < before.numValues) value op := by
  cases op with
  | slotAddr slot => simpa only [ContentsOperation, slots] using operation
  | globalAddr global => exact operation
  | refFreeze owner => exact operation.elim
  | fieldAddr owner field =>
    obtain ⟨member, mu, id, fields, descriptor, entry, typed, descriptorRow, fieldRow, writable⟩ := operation
    have ownerBound := operands owner (by simp [Op.uses])
    exact ⟨⟨member, ownerBound⟩, mu, id, fields, descriptor, entry,
      (prefixTypes owner ownerBound).trans typed, descriptorRow, fieldRow, writable⟩
  | snapshot _ owner | refElem owner _ | indexChecked owner _ _ | indexProven owner _ =>
    exact ⟨operation, operands owner (by simp [Op.uses])⟩
  | _ =>
    simpa only [ContentsOperation, typedPermissions, prefixTypes value bound] using operation

theorem ContentsClosed.restrict_extension
    {globalKinds : Array VarKind} {structs : Array StructDef} {before after : Func}
    (extension : PermissionGraphExtension before after)
    {oldTypes newTypes : Array (Option VTy)}
    (prefixTypes : ∀ v, v < before.numValues → oldTypes[v]? = newTypes[v]?)
    {authorized : ValueId → Prop}
    (closed : ContentsClosed globalKinds structs after newTypes authorized) :
    ContentsClosed globalKinds structs before oldTypes
      (fun value => authorized value ∧ value < before.numValues) := by
  constructor
  · exact fun _ member => member.2
  · intro block row param member authorized
    obtain ⟨next, nextRow, parameters, instructions⟩ := extension.blocks 0 block row
    have newMember : param ∈ next.params := by rwa [parameters]
    have allowed := closed.entry next nextRow param newMember authorized.1
    simpa only [typedPermissions, prefixTypes param.1 authorized.2] using allowed
  · intro block member value op definition authorized
    obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    obtain ⟨next, nextRow, parameters, instructions⟩ := extension.blocks index block row
    have nextMember := Array.mem_toList_iff.mpr (Array.mem_of_getElem? nextRow)
    exact (closed.definitions next nextMember value op (instructions _ definition) authorized.1).restrict
      extension.slots prefixTypes authorized.2 (extension.operands block member value op definition)
  · intro block member term definition edge edgeMember destination destinationRow entry entryMember authorized
    obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    obtain ⟨next, nextRow, parameters, instructions⟩ := extension.blocks index block row
    obtain ⟨newDestination, newDestinationRow, destinationParameters, _⟩ :=
      extension.blocks edge.1 destination destinationRow
    have newMember : entry ∈ newDestination.params.zip edge.2 := by
      rwa [destinationParameters]
    have nextMember := Array.mem_toList_iff.mpr (Array.mem_of_getElem? nextRow)
    exact ⟨closed.edges next nextMember term (instructions _ definition) edge edgeMember
        newDestination newDestinationRow entry newMember authorized.1,
      extension.arguments block member term definition edge edgeMember entry.2
        (List.of_mem_zip entryMember).2⟩

theorem permissionsFromTables_contents_antitone
    {globalKinds : Array VarKind} {structs : Array StructDef} {before after : Func}
    (extension : PermissionGraphExtension before after)
    {oldTypes newTypes : Array (Option VTy)}
    (prefixTypes : ∀ v, v < before.numValues → oldTypes[v]? = newTypes[v]?)
    {value : ValueId} (bound : value < before.numValues)
    (readonly : (permissionsAt (before.permissionsFromTables globalKinds structs oldTypes) value).2 = false) :
    (permissionsAt (after.permissionsFromTables globalKinds structs newTypes) value).2 = false := by
  cases allowed : (permissionsAt (after.permissionsFromTables globalKinds structs newTypes) value).2 with
  | false => rfl
  | true =>
    have closed := (contentsClosed_permissions globalKinds structs after newTypes).restrict_extension
      extension prefixTypes
    have oldAllowed := closed.permissions value ⟨allowed, bound⟩
    simp [readonly] at oldAllowed

end Goose.Lower.Validation

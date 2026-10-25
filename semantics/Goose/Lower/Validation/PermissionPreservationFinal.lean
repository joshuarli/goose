import Goose.Lower.Validation.PermissionPreservationTransport
import Goose.Lower.Validation.PermissionPreservationContents

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ContentsOperation.to_finished_function {globalKinds : Array VarKind} {structs : Array StructDef}
    {before after : Func} {types : Array (Option VTy)} {contents : ValueId → Prop}
    {value : ValueId} {op : Op} (slots : before.slots = after.slots)
    (operation : ContentsOperation globalKinds structs before types contents value op) :
    ContentsOperation globalKinds structs after types contents value op := by
  cases op <;> simp only [ContentsOperation, slots] at operation ⊢ <;> exact operation

theorem WritableOperation.to_finished_function {globalKinds : Array VarKind} {structs : Array StructDef}
    {before after : Func} {types : Array (Option VTy)} {contents : ValueId → Prop}
    {value : ValueId} {op : Op} (slots : before.slots = after.slots)
    (operation : WritableOperation globalKinds structs before types contents value op) :
    WritableOperation globalKinds structs after types contents value op := by
  cases op <;> simp only [WritableOperation, slots] at operation ⊢ <;> exact operation

theorem ContentsClosed.to_finished_function {globalKinds : Array VarKind} {structs : Array StructDef}
    {before after : Func} {types : Array (Option VTy)} {contents : ValueId → Prop}
    (closed : ContentsClosed globalKinds structs before types contents)
    (blocks : before.blocks = after.blocks) (slots : before.slots = after.slots) :
    ContentsClosed globalKinds structs after types contents := by
  constructor
  · simpa only [Func.numValues, blocks] using closed.bounded
  · simpa only [blocks] using closed.entry
  · intro block member value op instruction permitted
    rw [← blocks] at member
    exact (closed.definitions block member value op instruction permitted).to_finished_function slots
  · simpa only [blocks] using closed.edges

theorem WritableClosed.to_finished_function {globalKinds : Array VarKind} {structs : Array StructDef}
    {before after : Func} {types : Array (Option VTy)} {writable contents : ValueId → Prop}
    (closed : WritableClosed globalKinds structs before types writable contents)
    (blocks : before.blocks = after.blocks) (slots : before.slots = after.slots) :
    WritableClosed globalKinds structs after types writable contents := by
  constructor
  · simpa only [Func.numValues, blocks] using closed.bounded
  · simpa only [blocks] using closed.entry
  · intro block member value op instruction permitted
    rw [← blocks] at member
    exact (closed.definitions block member value op instruction permitted).to_finished_function slots
  · simpa only [blocks] using closed.edges

theorem checkPermissions_of_lowered_evidence {le : LEnv} {state : LS} {module : GIR.Module}
    {func : Func} (blocks : (permissionFunc le state).blocks = func.blocks)
    (slots : (permissionFunc le state).slots = func.slots)
    (globals : le.globals.map (·.2) = module.globals.map (·.kind))
    (structs : le.mod.structs = module.structs)
    (rules : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      PermissionRule module func state.vals (WritableEvidence le state)
        (ContentsEvidence le state) instruction) (label : String) :
    checkPermissions module label func state.vals = .ok () := by
  apply checkPermissions_of_rules rules
  · intro value evidence
    obtain ⟨writable, contents, bindings, elements, _, _, permitted⟩ := evidence
    have actualBindings := bindings.to_finished_function blocks slots
    have actualElements := elements.to_finished_function blocks slots
    simpa only [Func.permissions, globals, structs] using
      actualBindings.permissions actualElements value permitted
  · intro value evidence
    obtain ⟨contents, elements, _, permitted⟩ := evidence
    have actualElements := elements.to_finished_function blocks slots
    simpa only [Func.permissions, globals, structs] using actualElements.permissions value permitted

#print axioms ContentsClosed.to_finished_function
#print axioms WritableClosed.to_finished_function
#print axioms checkPermissions_of_lowered_evidence

end Goose.Lower.Validation

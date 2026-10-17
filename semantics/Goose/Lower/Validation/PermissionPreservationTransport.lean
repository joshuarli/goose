import Goose.Lower.Validation.PermissionPreservationGraph

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem WritableOperation.replace_types {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {before after : Array (Option VTy)} {writable contents : ValueId → Prop}
    {value : ValueId} {op : Op}
    (agreement : ∀ candidate, writable candidate ∨ contents candidate → before[candidate]? = after[candidate]?)
    (member : writable value)
    (operation : WritableOperation globalKinds structs func before contents value op) :
    WritableOperation globalKinds structs func after contents value op := by
  cases op with
  | slotAddr _ | globalAddr _ => exact operation
  | refFreeze _ => contradiction
  | fieldAddr owner index =>
    obtain ⟨permitted, mu, id, fields, descriptor, field, typed, descriptorRow, fieldRow, binding⟩ := operation
    refine ⟨permitted, mu, id, fields, descriptor, field, ?_, descriptorRow, fieldRow, binding⟩
    rw [← agreement owner (Or.inr permitted)]
    exact typed
  | ownerBorrow _ | snapshot _ _ | refElem _ _ | indexChecked _ _ _ | indexProven _ _ => exact operation
  | _ => simpa only [WritableOperation, typedPermissions, ← agreement value (Or.inl member)] using operation

theorem WritableClosed.replace_types {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {before after : Array (Option VTy)} {writable contents : ValueId → Prop}
    (closed : WritableClosed globalKinds structs func before writable contents)
    (agreement : ∀ candidate, writable candidate ∨ contents candidate → before[candidate]? = after[candidate]?) :
    WritableClosed globalKinds structs func after writable contents := by
  constructor
  · exact closed.bounded
  · intro block row param member permitted
    have typed := closed.entry block row param member permitted
    simpa only [typedPermissions, ← agreement param.1 (Or.inl permitted)] using typed
  · intro block blockMember value op member permitted
    exact (closed.definitions block blockMember value op member permitted).replace_types agreement permitted
  · exact closed.edges

theorem PermissionTransfer.mono {profile : ArtifactProfile} {writable contents widerWritable widerContents : ValueId → Prop}
    {value : ValueId} {ty : Ty} (allowed : PermissionTransfer profile writable contents value ty)
    (bindings : ∀ candidate, writable candidate → widerWritable candidate)
    (elements : ∀ candidate, contents candidate → widerContents candidate) :
    PermissionTransfer profile widerWritable widerContents value ty := by
  cases ty with
  | ref mu referent =>
    cases mu with
    | readOnly => trivial
    | mutable =>
      cases profile <;> cases referent <;> simp only [PermissionTransfer, reduceCtorEq, ↓reduceIte] at allowed ⊢ <;>
        first | exact elements value allowed
              | exact ⟨bindings value allowed.1, elements value allowed.2⟩
              | exact bindings value allowed
  | _ => trivial

theorem PermissionRule.mono {module : GIR.Module} {func : Func} {types : Array (Option VTy)}
    {writable contents widerWritable widerContents : ValueId → Prop} {instruction : Inst}
    (rule : PermissionRule module func types writable contents instruction)
    (bindings : ∀ candidate, writable candidate → widerWritable candidate)
    (elements : ∀ candidate, contents candidate → widerContents candidate) :
    PermissionRule module func types widerWritable widerContents instruction := by
  constructor
  · intro owner value origin shape
    exact bindings owner (rule.storeBinding owner value origin shape)
  · intro owner value origin mu ty shape typed
    exact (rule.storeValue owner value origin mu ty shape typed).mono bindings elements
  · intro owner mutation
    exact elements owner (rule.mutation owner mutation)
  · intro value owner shape
    exact elements owner (rule.ownerBorrow value owner shape)
  · intro owner value origin shape
    have both := rule.replacement owner value origin shape
    exact ⟨bindings owner both.1, elements owner both.2⟩
  · intro value mode owner ty shape typed
    exact elements value (rule.snapshot value mode owner ty shape typed)
  · intro value callee args origin descriptor shape row entry member
    exact (rule.call value callee args origin descriptor shape row entry member).mono bindings elements
  · intro slot value origin descriptor shape row
    exact (rule.binding slot value origin descriptor shape row).mono bindings elements
  · intro values origin shape entry member
    exact (rule.result values origin shape entry member).mono bindings elements

#print axioms WritableClosed.replace_types
#print axioms PermissionRule.mono

end Goose.Lower.Validation

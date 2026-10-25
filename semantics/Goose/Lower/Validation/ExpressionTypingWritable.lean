import Goose.Lower.Validation.ExpressionTypingAuthority

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def WritablePresent (caps : Array (Bool × Bool)) (authorized : ValueId → Prop) : Prop :=
  ∀ value, authorized value → (permissionsAt caps value).1 = true

theorem WritablePresent.bound {caps : Array (Bool × Bool)} {authorized : ValueId → Prop}
    (present : WritablePresent caps authorized) {value : ValueId} (member : authorized value) :
    value < caps.size := by
  have checked := present value member
  by_cases inside : value < caps.size
  · exact inside
  · have missing : caps[value]? = none := Array.getElem?_eq_none (xs := caps) (i := value) (Nat.le_of_not_gt inside)
    simp [permissionsAt, missing] at checked

theorem WritablePresent.set_meet {caps : Array (Bool × Bool)} {authorized : ValueId → Prop}
    (present : WritablePresent caps authorized) (value : ValueId) (capability : Bool × Bool)
    (allowed : authorized value → capability.1 = true) :
    WritablePresent (caps.set! value (meetPermissions (permissionsAt caps value) capability)) authorized := by
  intro other member
  by_cases same : value = other
  · subst other
    have bounded := present.bound member
    have existing := present value member
    have permitted := allowed member
    simp only [permissionsAt, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_self_of_lt bounded, Option.getD_some, meetPermissions]
    exact Bool.and_eq_true_iff.mpr ⟨existing, permitted⟩
  · simpa only [permissionsAt, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne same] using present other member

theorem writablePresent_replicate {authorized : ValueId → Prop} {size : Nat}
    (bounded : ∀ value, authorized value → value < size) :
    WritablePresent (Array.replicate size (true, true)) authorized := by
  intro value member
  simp [permissionsAt, bounded value member]

def WritableOperation (globalKinds : Array VarKind) (structs : Array StructDef)
    (func : Func) (types : Array (Option VTy)) (contents : ValueId → Prop)
    (value : ValueId) : Op → Prop
  | .slotAddr slot => ∃ descriptor, func.slots[slot]? = some descriptor ∧ descriptor.kind = .mutable
  | .globalAddr global => globalKinds[global]? = some .mutable
  | .refFreeze _ => False
  | .fieldAddr owner index => contents owner ∧ ∃ mu id fields descriptor field,
      types[owner]? = some (some (.data (.ref mu (.structT id fields)))) ∧
      structs[id]? = some descriptor ∧ descriptor.fields[index]? = some field ∧ field.binding = .mutable
  | .ownerBorrow owner | .snapshot _ owner | .refElem owner _ | .indexChecked owner _ _ | .indexProven owner _ => contents owner
  | _ => (typedPermissions types value).1 = true

theorem WritableOperation.check {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {types : Array (Option VTy)} {contents : ValueId → Prop}
    {value : ValueId} {op : Op} {caps : Array (Bool × Bool)}
    (operation : WritableOperation globalKinds structs func types contents value op)
    (present : ContentsPresent caps contents) :
    (func.permissionOfOp globalKinds structs types caps value op).1 = true := by
  cases op with
  | slotAddr slot =>
    obtain ⟨descriptor, row, mutable⟩ := operation
    simp [Func.permissionOfOp, row, mutable]
  | globalAddr global =>
    change globalKinds[global]? = some .mutable at operation
    simp [Func.permissionOfOp, operation]
  | refFreeze _ => contradiction
  | fieldAddr owner index =>
    obtain ⟨member, mu, id, fields, descriptor, field, typed, descriptorRow, fieldRow, writable⟩ := operation
    simp [Func.permissionOfOp, typed, descriptorRow, fieldRow, writable, present owner member]
  | ownerBorrow owner | snapshot _ owner | refElem owner _ | indexChecked owner _ _ | indexProven owner _ =>
    exact present owner operation
  | _ => exact operation

structure WritableClosed (globalKinds : Array VarKind) (structs : Array StructDef)
    (func : Func) (types : Array (Option VTy)) (authorized contents : ValueId → Prop) : Prop where
  bounded : ∀ value, authorized value → value < func.numValues
  entry : ∀ block, func.blocks[0]? = some block → ∀ param ∈ block.params,
    authorized param.1 → (typedPermissions types param.1).1 = true
  definitions : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
    authorized value → WritableOperation globalKinds structs func types contents value op
  edges : ∀ block ∈ func.blocks.toList, ∀ term, Inst.term term ∈ block.insts →
    ∀ edge ∈ term.permissionEdges, ∀ destination, func.blocks[edge.1]? = some destination →
      ∀ entry ∈ destination.params.zip edge.2, authorized entry.1.1 → authorized entry.2

theorem WritableClosed.round {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {types : Array (Option VTy)} {authorized contents : ValueId → Prop}
    (closed : WritableClosed globalKinds structs func types authorized contents) {caps : Array (Bool × Bool)}
    (present : WritablePresent caps authorized)
    (contentPresent : ContentsPresent caps contents) :
    WritablePresent (func.permissionRound globalKinds structs types caps) authorized := by
  unfold Func.permissionRound
  cases entryRow : func.blocks[0]? with
  | none =>
    simp only [Id.run, pure, bind]
    apply array_forIn_invariant (invariant := fun values => WritablePresent values authorized)
    · intro block blockMember current prior
      simp only [ForInStep.value]
      apply list_forIn_invariant (invariant := fun values => WritablePresent values authorized)
      · intro inst instMember next checked
        cases inst with
        | «def» value op =>
          exact checked.set_meet value _ (fun member =>
            (closed.definitions block blockMember value op instMember member).check contentPresent)
        | eff effect => exact checked
        | term term =>
          simp only [ForInStep.value]
          apply list_forIn_invariant (invariant := fun values => WritablePresent values authorized)
          · intro edge edgeMember next checked
            obtain ⟨target, args⟩ := edge
            cases destinationRow : func.blocks[target]? with
            | none => simpa only [ForInStep.value] using checked
            | some destination =>
              simp only [ForInStep.value]
              apply list_forIn_invariant (invariant := fun values => WritablePresent values authorized)
              · intro entry member next checked
                obtain ⟨⟨value, ty⟩, arg⟩ := entry
                apply checked.set_meet
                intro allowed
                exact present arg (closed.edges block blockMember term instMember (target, args)
                  edgeMember destination destinationRow ((value, ty), arg) member allowed)
              · exact checked
          · exact checked
      · exact prior
    · exact present
  | some block =>
    simp only [Id.run, pure, bind]
    apply array_forIn_invariant (invariant := fun values => WritablePresent values authorized)
    · intro block blockMember current prior
      simp only [ForInStep.value]
      apply list_forIn_invariant (invariant := fun values => WritablePresent values authorized)
      · intro inst instMember next checked
        cases inst with
        | «def» value op =>
          exact checked.set_meet value _ (fun member =>
            (closed.definitions block blockMember value op instMember member).check contentPresent)
        | eff effect => exact checked
        | term term =>
          simp only [ForInStep.value]
          apply list_forIn_invariant (invariant := fun values => WritablePresent values authorized)
          · intro edge edgeMember next checked
            obtain ⟨target, args⟩ := edge
            cases destinationRow : func.blocks[target]? with
            | none => simpa only [ForInStep.value] using checked
            | some destination =>
              simp only [ForInStep.value]
              apply list_forIn_invariant (invariant := fun values => WritablePresent values authorized)
              · intro entry member next checked
                obtain ⟨⟨value, ty⟩, arg⟩ := entry
                apply checked.set_meet
                intro allowed
                exact present arg (closed.edges block blockMember term instMember (target, args)
                  edgeMember destination destinationRow ((value, ty), arg) member allowed)
              · exact checked
          · exact checked
      · exact prior
    · apply list_forIn_invariant (invariant := fun values => WritablePresent values authorized)
      · intro entry member next checked
        obtain ⟨value, ty⟩ := entry
        exact checked.set_meet value _ (closed.entry block entryRow (value, ty) member)
      · exact present

theorem WritableClosed.permissions {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {types : Array (Option VTy)} {authorized contents : ValueId → Prop}
    (closed : WritableClosed globalKinds structs func types authorized contents)
    (contentClosed : ContentsClosed globalKinds structs func types contents) :
    WritablePresent (func.permissionsFromTables globalKinds structs types) authorized := by
  have both := permissionsFromTables_invariant
    (invariant := fun caps => WritablePresent caps authorized ∧ ContentsPresent caps contents)
    (fun _ present => ⟨closed.round present.1 present.2, contentClosed.round present.2⟩)
    ⟨writablePresent_replicate closed.bounded, contentsPresent_replicate contentClosed.bounded⟩
  exact both.1

#print axioms WritableClosed.permissions

end Goose.Lower.Validation

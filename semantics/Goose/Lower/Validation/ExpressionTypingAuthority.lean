import Goose.Lower.Validation.ExpressionTypingPermissions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def ContentsPresent (caps : Array (Bool × Bool)) (authorized : ValueId → Prop) : Prop :=
  ∀ value, authorized value → (permissionsAt caps value).2 = true

theorem ContentsPresent.bound {caps : Array (Bool × Bool)} {authorized : ValueId → Prop}
    (present : ContentsPresent caps authorized) {value : ValueId} (member : authorized value) :
    value < caps.size := by
  have checked := present value member
  by_cases inside : value < caps.size
  · exact inside
  · have missing : caps[value]? = none := Array.getElem?_eq_none (xs := caps) (i := value) (Nat.le_of_not_gt inside)
    simp [permissionsAt, missing] at checked

theorem ContentsPresent.set_meet {caps : Array (Bool × Bool)} {authorized : ValueId → Prop}
    (present : ContentsPresent caps authorized) (value : ValueId) (capability : Bool × Bool)
    (allowed : authorized value → capability.2 = true) :
    ContentsPresent (caps.set! value (meetPermissions (permissionsAt caps value) capability)) authorized := by
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

theorem contentsPresent_replicate {authorized : ValueId → Prop} {size : Nat}
    (bounded : ∀ value, authorized value → value < size) :
    ContentsPresent (Array.replicate size (true, true)) authorized := by
  intro value member
  simp [permissionsAt, bounded value member]

def ContentsOperation (globalKinds : Array VarKind) (structs : Array StructDef)
    (func : Func) (types : Array (Option VTy)) (authorized : ValueId → Prop)
    (value : ValueId) : Op → Prop
  | .slotAddr slot => ∃ descriptor, func.slots[slot]? = some descriptor
  | .globalAddr global => ∃ kind, globalKinds[global]? = some kind
  | .refFreeze _ => False
  | .fieldAddr owner index => authorized owner ∧ ∃ mu id fields descriptor field,
      types[owner]? = some (some (.data (.ref mu (.structT id fields)))) ∧
      structs[id]? = some descriptor ∧ descriptor.fields[index]? = some field ∧ field.contents = .mutable
  | .snapshot _ owner | .refElem owner _ | .indexChecked owner _ _ | .indexProven owner _ => authorized owner
  | _ => (typedPermissions types value).2 = true

theorem ContentsOperation.check {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {types : Array (Option VTy)} {authorized : ValueId → Prop}
    {value : ValueId} {op : Op} {caps : Array (Bool × Bool)}
    (operation : ContentsOperation globalKinds structs func types authorized value op)
    (present : ContentsPresent caps authorized) :
    (func.permissionOfOp globalKinds structs types caps value op).2 = true := by
  cases op with
  | slotAddr slot =>
    obtain ⟨descriptor, row⟩ := operation
    simp [Func.permissionOfOp, row]
  | globalAddr global =>
    obtain ⟨kind, row⟩ := operation
    simp [Func.permissionOfOp, row]
  | refFreeze _ => contradiction
  | fieldAddr owner index =>
    obtain ⟨member, mu, id, fields, descriptor, field, typed, descriptorRow, fieldRow, writable⟩ := operation
    simp [Func.permissionOfOp, typed, descriptorRow, fieldRow, writable, present owner member]
  | snapshot _ owner | refElem owner _ | indexChecked owner _ _ | indexProven owner _ =>
    exact present owner operation
  | _ => exact operation

structure ContentsClosed (globalKinds : Array VarKind) (structs : Array StructDef)
    (func : Func) (types : Array (Option VTy)) (authorized : ValueId → Prop) : Prop where
  bounded : ∀ value, authorized value → value < func.numValues
  entry : ∀ block, func.blocks[0]? = some block → ∀ param ∈ block.params,
    authorized param.1 → (typedPermissions types param.1).2 = true
  definitions : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
    authorized value → ContentsOperation globalKinds structs func types authorized value op
  edges : ∀ block ∈ func.blocks.toList, ∀ term, Inst.term term ∈ block.insts →
    ∀ edge ∈ term.permissionEdges, ∀ destination, func.blocks[edge.1]? = some destination →
      ∀ entry ∈ destination.params.zip edge.2, authorized entry.1.1 → authorized entry.2

theorem ContentsClosed.round {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {types : Array (Option VTy)} {authorized : ValueId → Prop}
    (closed : ContentsClosed globalKinds structs func types authorized) {caps : Array (Bool × Bool)}
    (present : ContentsPresent caps authorized) :
    ContentsPresent (func.permissionRound globalKinds structs types caps) authorized := by
  unfold Func.permissionRound
  cases entryRow : func.blocks[0]? with
  | none =>
    simp only [Id.run, pure, bind]
    apply array_forIn_invariant (invariant := fun values => ContentsPresent values authorized)
    · intro block blockMember current prior
      simp only [ForInStep.value]
      apply list_forIn_invariant (invariant := fun values => ContentsPresent values authorized)
      · intro inst instMember next checked
        cases inst with
        | «def» value op =>
          exact checked.set_meet value _ (fun member =>
            (closed.definitions block blockMember value op instMember member).check present)
        | eff effect => exact checked
        | term term =>
          simp only [ForInStep.value]
          apply list_forIn_invariant (invariant := fun values => ContentsPresent values authorized)
          · intro edge edgeMember next checked
            obtain ⟨target, args⟩ := edge
            cases destinationRow : func.blocks[target]? with
            | none => simpa only [ForInStep.value] using checked
            | some destination =>
              simp only [ForInStep.value]
              apply list_forIn_invariant (invariant := fun values => ContentsPresent values authorized)
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
    apply array_forIn_invariant (invariant := fun values => ContentsPresent values authorized)
    · intro block blockMember current prior
      simp only [ForInStep.value]
      apply list_forIn_invariant (invariant := fun values => ContentsPresent values authorized)
      · intro inst instMember next checked
        cases inst with
        | «def» value op =>
          exact checked.set_meet value _ (fun member =>
            (closed.definitions block blockMember value op instMember member).check present)
        | eff effect => exact checked
        | term term =>
          simp only [ForInStep.value]
          apply list_forIn_invariant (invariant := fun values => ContentsPresent values authorized)
          · intro edge edgeMember next checked
            obtain ⟨target, args⟩ := edge
            cases destinationRow : func.blocks[target]? with
            | none => simpa only [ForInStep.value] using checked
            | some destination =>
              simp only [ForInStep.value]
              apply list_forIn_invariant (invariant := fun values => ContentsPresent values authorized)
              · intro entry member next checked
                obtain ⟨⟨value, ty⟩, arg⟩ := entry
                apply checked.set_meet
                intro allowed
                exact present arg (closed.edges block blockMember term instMember (target, args)
                  edgeMember destination destinationRow ((value, ty), arg) member allowed)
              · exact checked
          · exact checked
      · exact prior
    · apply list_forIn_invariant (invariant := fun values => ContentsPresent values authorized)
      · intro entry member next checked
        obtain ⟨value, ty⟩ := entry
        exact checked.set_meet value _ (closed.entry block entryRow (value, ty) member)
      · exact present

theorem ContentsClosed.permissions {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {types : Array (Option VTy)} {authorized : ValueId → Prop}
    (closed : ContentsClosed globalKinds structs func types authorized) :
    ContentsPresent (func.permissionsFromTables globalKinds structs types) authorized :=
  permissionsFromTables_invariant (invariant := fun caps => ContentsPresent caps authorized)
    (fun _ present => closed.round present)
    (contentsPresent_replicate closed.bounded)

end Goose.Lower.Validation

import Goose.Lower.Validation.ExpressionTypingEdges

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def NonIntegerParameters (func : Func) (authorized : ValueId → Prop) : Prop :=
  ∀ block ∈ func.blocks.toList, ∀ param ∈ block.params,
    authorized param.1 → ∀ intTy, param.2 ≠ .data (.int intTy)

theorem NonIntegerParameters.empty (func : Func) : NonIntegerParameters func (fun _ => False) := by
  intro block blockMember param member impossible
  cases impossible

theorem NonIntegerParameters.mono {func : Func} {first second : ValueId → Prop}
    (checked : NonIntegerParameters func second) (inclusion : ∀ value, first value → second value) :
    NonIntegerParameters func first := by
  intro block blockMember param member permitted
  exact checked block blockMember param member (inclusion param.1 permitted)

theorem NonIntegerParameters.union {func : Func} {first second : ValueId → Prop}
    (left : NonIntegerParameters func first) (right : NonIntegerParameters func second) :
    NonIntegerParameters func (fun value => first value ∨ second value) := by
  intro block blockMember param member permitted
  exact permitted.elim (left block blockMember param member) (right block blockMember param member)

theorem NonIntegerParameters.emitDef_preserve {le : LEnv} {before after : LS}
    {value : ValueId} {op : Op} {current : BlockId} {authorized : ValueId → Prop}
    (live : before.cur = some current) (run : emitDef op le before = (value, after))
    (checked : NonIntegerParameters (permissionFunc le before) authorized) :
    NonIntegerParameters (permissionFunc le after) authorized := by
  intro block blockMember param member permitted
  obtain ⟨old, oldMember, params, _⟩ := emitDef_frame_blocks live run blockMember
  exact checked old oldMember param (by rw [← params]; exact member) permitted

theorem nonIntegerParameters_fresh_definition {le : LEnv} {before after : LS}
    {value : ValueId} {op : Op} {current : BlockId}
    (checked : before.DenseDefinitions) (live : before.cur = some current)
    (run : emitDef op le before = (value, after)) :
    NonIntegerParameters (permissionFunc le after) (fun candidate => candidate = value) := by
  intro block blockMember param member permitted
  have bound := emitDef_frame_param_bound checked live run blockMember member
  have fresh := (emitDef_fresh_size live run).1
  rw [permitted, fresh] at bound
  exact (Nat.lt_irrefl _ bound).elim

theorem NonIntegerParameters.emitTerm {le : LEnv} {before after : LS}
    {result : Unit} {term : Term} {current : BlockId} {authorized : ValueId → Prop}
    (live : before.cur = some current) (run : emitTerm term le before = (result, after))
    (checked : NonIntegerParameters (permissionFunc le before) authorized) :
    NonIntegerParameters (permissionFunc le after) authorized := by
  intro block blockMember param member permitted
  obtain ⟨old, oldMember, params, _⟩ := emitTerm_frame_blocks live run blockMember
  exact checked old oldMember param (by rw [← params]; exact member) permitted

theorem NonIntegerParameters.newBlock_preserve {le : LEnv} {before after : LS}
    {types : List VTy} {result : BlockId × List ValueId} {authorized : ValueId → Prop}
    (run : newBlock types le before = (result, after))
    (bounded : ∀ value, authorized value → value < before.vals.size)
    (checked : NonIntegerParameters (permissionFunc le before) authorized) :
    NonIntegerParameters (permissionFunc le after) authorized := by
  intro block blockMember param member permitted
  rcases newBlock_frame_blocks run blockMember with old | rfl
  · exact checked block old param member permitted
  · have fresh := paramIds_lower_bound member
    exact (Nat.not_lt_of_ge fresh (bounded param.1 permitted)).elim

theorem nonIntegerParameters_newBlock_fresh {le : LEnv} {before after : LS}
    {types : List VTy} {result : BlockId × List ValueId}
    (run : newBlock types le before = (result, after)) (checked : before.DenseDefinitions)
    (noninteger : ∀ ty ∈ types, ∀ intTy, ty ≠ .data (.int intTy)) :
    NonIntegerParameters (permissionFunc le after)
      (fun candidate => before.vals.size ≤ candidate ∧ candidate < after.vals.size) := by
  intro block blockMember param member permitted
  rcases newBlock_frame_blocks run blockMember with old | rfl
  · have previous := permissionFunc_param_bound checked old member
    exact (Nat.not_lt_of_ge permitted.1 previous).elim
  · exact noninteger param.2 (List.of_mem_zip member).2

theorem ContentsClosed.empty (globalKinds : Array VarKind) (structs : Array StructDef)
    (func : Func) (types : Array (Option VTy)) :
    ContentsClosed globalKinds structs func types (fun _ => False) := by
  constructor
  · intro value impossible; cases impossible
  · intro block row param member impossible; cases impossible
  · intro block blockMember value op member impossible; cases impossible
  · intro block blockMember term member edge edgeMember destination row entry entryMember impossible
    cases impossible

theorem ContentsOperation.replace_types {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {before after : Array (Option VTy)} {authorized : ValueId → Prop}
    {value : ValueId} {op : Op}
    (agreement : ∀ candidate, authorized candidate → before[candidate]? = after[candidate]?)
    (member : authorized value)
    (operation : ContentsOperation globalKinds structs func before authorized value op) :
    ContentsOperation globalKinds structs func after authorized value op := by
  cases op with
  | slotAddr _ | globalAddr _ => exact operation
  | refFreeze _ => contradiction
  | fieldAddr owner index =>
    obtain ⟨permitted, mu, id, fields, descriptor, field, typed, descriptorRow, fieldRow, writable⟩ := operation
    refine ⟨permitted, mu, id, fields, descriptor, field, ?_, descriptorRow, fieldRow, writable⟩
    rw [← agreement owner permitted]
    exact typed
  | snapshot _ _ | refElem _ _ | indexChecked _ _ _ | indexProven _ _ => exact operation
  | _ => simpa only [ContentsOperation, typedPermissions, ← agreement value member] using operation

theorem ContentsClosed.replace_types {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {before after : Array (Option VTy)} {authorized : ValueId → Prop}
    (closed : ContentsClosed globalKinds structs func before authorized)
    (agreement : ∀ candidate, authorized candidate → before[candidate]? = after[candidate]?) :
    ContentsClosed globalKinds structs func after authorized := by
  constructor
  · exact closed.bounded
  · intro block row param member permitted
    have typed := closed.entry block row param member permitted
    simpa only [typedPermissions, ← agreement param.1 permitted] using typed
  · intro block blockMember value op member permitted
    exact (closed.definitions block blockMember value op member permitted).replace_types agreement permitted
  · exact closed.edges

#print axioms ContentsClosed.replace_types
#print axioms nonIntegerParameters_newBlock_fresh

end Goose.Lower.Validation

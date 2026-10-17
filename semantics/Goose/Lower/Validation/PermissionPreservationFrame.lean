import Goose.Lower.Validation.PermissionPreservation
import Goose.Lower.Validation.ExpressionTypingFrame

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem WritableOperation.monoContents {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {types : Array (Option VTy)} {first second : ValueId → Prop}
    {value : ValueId} {op : Op} (inclusion : ∀ candidate, first candidate → second candidate)
    (operation : WritableOperation globalKinds structs func types first value op) :
    WritableOperation globalKinds structs func types second value op := by
  cases op with
  | fieldAddr owner index => exact ⟨inclusion owner operation.1, operation.2⟩
  | snapshot _ owner | refElem owner _ | indexChecked owner _ _ | indexProven owner _ =>
    exact inclusion owner operation
  | _ => exact operation

theorem typedPermissions_binding_retained {before after : LS} (extension : TypePrefix before after)
    {value : ValueId} (typed : (typedPermissions before.vals value).1 = true) :
    (typedPermissions after.vals value).1 = true := by
  cases row : before.vals[value]? with
  | none => simp [typedPermissions, row] at typed
  | some cell =>
    cases cell with
    | none => simp [typedPermissions, row] at typed
    | some ty =>
      have recorded := extension value ty row
      simpa only [typedPermissions, row, recorded] using typed

theorem WritableOperation.retained {le : LEnv} {before after : LS} {contents : ValueId → Prop}
    {value : ValueId} {op : Op} (extension : TypePrefix before after)
    (operation : WritableOperation (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals contents value op) :
    WritableOperation (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals contents value op := by
  cases op with
  | slotAddr _ | globalAddr _ => exact operation
  | refFreeze _ => contradiction
  | fieldAddr owner index =>
    obtain ⟨member, mu, id, fields, descriptor, field, typed, descriptorRow, fieldRow, writable⟩ := operation
    exact ⟨member, mu, id, fields, descriptor, field, extension owner _ typed, descriptorRow, fieldRow, writable⟩
  | snapshot _ _ | refElem _ _ | indexChecked _ _ _ | indexProven _ _ => exact operation
  | _ => exact typedPermissions_binding_retained extension operation

theorem WritableClosed.emitDef_preserve {le : LEnv} {before after : LS}
    {value : ValueId} {op : Op} {current : BlockId} {authorized contents : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef op le before = (value, after))
    (closed : WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized contents) :
    WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized contents := by
  have extension := types_emitDef op le before value after run
  have afterDense := (dense_emitDef op le before value after run checked bounded).1
  obtain ⟨fresh, size⟩ := emitDef_fresh_size live run
  have oldBound : ∀ candidate, authorized candidate → candidate < before.vals.size := by
    intro candidate member
    simpa only [permissionFunc_numValues checked le] using closed.bounded candidate member
  constructor
  · intro candidate member
    rw [permissionFunc_numValues afterDense le, size]
    exact Nat.lt_succ_of_lt (oldBound candidate member)
  · intro block row param member permitted
    obtain ⟨old, oldRow, params⟩ := emitDef_frame_at live run row
    have oldMember : param ∈ old.params := by rw [← params]; exact member
    exact typedPermissions_binding_retained extension (closed.entry old oldRow param oldMember permitted)
  · intro block blockMember result actual member permitted
    obtain ⟨old, oldMember, _, instructions⟩ := emitDef_frame_blocks live run blockMember
    have oldInstruction : Inst.def result actual ∈ old.insts := by
      rcases instructions with same | same
      · rw [same] at member; exact member
      · rw [same, List.mem_append, List.mem_singleton] at member
        rcases member with member | equation
        · exact member
        · have equal := (Inst.def.inj equation).1
          have impossible := oldBound result permitted
          rw [equal] at impossible
          exact (Nat.lt_irrefl _ impossible).elim
    exact (closed.definitions old oldMember result actual oldInstruction permitted).retained extension
  · intro block blockMember term member edge edgeMember destination row entry entryMember permitted
    obtain ⟨old, oldMember, _, instructions⟩ := emitDef_frame_blocks live run blockMember
    have oldInstruction : Inst.term term ∈ old.insts := by
      rcases instructions with same | same
      · rw [same] at member; exact member
      · rw [same, List.mem_append, List.mem_singleton] at member
        rcases member with member | impossible
        · exact member
        · cases impossible
    obtain ⟨oldDestination, oldRow, params⟩ := emitDef_frame_at live run row
    have oldEntry : entry ∈ oldDestination.params.zip edge.2 := by rw [← params]; exact entryMember
    exact closed.edges old oldMember term oldInstruction edge edgeMember oldDestination oldRow entry oldEntry permitted

theorem writableClosed_fresh_definition {le : LEnv} {before after : LS} {value : ValueId}
    {op : Op} {current : BlockId} {contents : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef op le before = (value, after))
    (operation : WritableOperation (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals contents value op) :
    WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals (fun candidate => candidate = value) contents := by
  have afterDense := (dense_emitDef op le before value after run checked bounded).1
  obtain ⟨fresh, size⟩ := emitDef_fresh_size live run
  subst value
  constructor
  · intro candidate member
    subst candidate
    rw [permissionFunc_numValues afterDense le, size]
    exact Nat.lt_succ_self _
  · intro block blockRow param member authorized
    have blockMember := Array.mem_of_getElem? blockRow
    have bound := emitDef_frame_param_bound checked live run (Array.mem_toList_iff.mpr blockMember) member
    rw [authorized] at bound
    exact (Nat.lt_irrefl _ bound).elim
  · intro block blockMember result actual member authorized
    subst result
    have same := emitDef_frame_fresh_operation checked live run blockMember member
    subst actual
    exact operation
  · intro block blockMember term termMember edge edgeMember destination destinationRow entry member authorized
    have destinationMember := Array.mem_of_getElem? destinationRow
    have paramMember := (List.of_mem_zip member).1
    have bound := emitDef_frame_param_bound checked live run
      (Array.mem_toList_iff.mpr destinationMember) paramMember
    rw [authorized] at bound
    exact (Nat.lt_irrefl _ bound).elim

theorem WritableClosed.monoContents {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {types : Array (Option VTy)} {authorized first second : ValueId → Prop}
    (closed : WritableClosed globalKinds structs func types authorized first)
    (inclusion : ∀ candidate, first candidate → second candidate) :
    WritableClosed globalKinds structs func types authorized second := by
  refine ⟨closed.bounded, closed.entry, ?_, closed.edges⟩
  intro block blockMember value op member permitted
  exact (closed.definitions block blockMember value op member permitted).monoContents inclusion

theorem WritableClosed.union {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {types : Array (Option VTy)} {first second contents : ValueId → Prop}
    (left : WritableClosed globalKinds structs func types first contents)
    (right : WritableClosed globalKinds structs func types second contents) :
    WritableClosed globalKinds structs func types (fun value => first value ∨ second value) contents := by
  constructor
  · intro value member
    exact member.elim (left.bounded value) (right.bounded value)
  · intro block row param member permitted
    exact permitted.elim (left.entry block row param member) (right.entry block row param member)
  · intro block blockMember value op member permitted
    exact permitted.elim (left.definitions block blockMember value op member)
      (right.definitions block blockMember value op member)
  · intro block blockMember term member edge edgeMember destination row entry entryMember permitted
    rcases permitted with permitted | permitted
    · exact Or.inl (left.edges block blockMember term member edge edgeMember destination row entry entryMember permitted)
    · exact Or.inr (right.edges block blockMember term member edge edgeMember destination row entry entryMember permitted)

theorem WritableClosed.emitDef_extend {le : LEnv} {before after : LS}
    {value : ValueId} {op : Op} {current : BlockId} {authorized contents : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef op le before = (value, after))
    (closed : WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized contents)
    (operation : WritableOperation (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals contents value op) :
    WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals (fun candidate => authorized candidate ∨ candidate = value) contents :=
  (closed.emitDef_preserve checked bounded live run).union
    (writableClosed_fresh_definition checked bounded live run operation)

theorem WritableClosed.newBlock_preserve {le : LEnv} {before after : LS} {types : List VTy}
    {result : BlockId × List ValueId} {authorized contents : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : newBlock types le before = (result, after))
    (closed : WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized contents) :
    WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized contents := by
  have extension := types_newBlock types le before result after run
  have afterDense := (dense_newBlock types le before result after run checked bounded).1
  have size : before.vals.size ≤ after.vals.size := by
    rw [newBlock_run_general] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    simp only [array_size_pushParamTypes]
    omega
  have oldBound : ∀ candidate, authorized candidate → candidate < before.vals.size := by
    intro candidate member
    simpa only [permissionFunc_numValues checked le] using closed.bounded candidate member
  constructor
  · intro value member
    rw [permissionFunc_numValues afterDense le]
    exact Nat.lt_of_lt_of_le (oldBound value member) size
  · intro block row param member permitted
    rcases newBlock_frame_at run row with oldRow | rfl
    · exact typedPermissions_binding_retained extension (closed.entry block oldRow param member permitted)
    · have fresh := paramIds_lower_bound member
      have old := oldBound param.1 permitted
      exact (Nat.not_lt_of_ge fresh old).elim
  · intro block blockMember value op member permitted
    rcases newBlock_frame_blocks run blockMember with oldBlock | rfl
    · exact (closed.definitions block oldBlock value op member permitted).retained extension
    · simp at member
  · intro block blockMember term member edge edgeMember destination row entry entryMember permitted
    rcases newBlock_frame_blocks run blockMember with oldBlock | rfl
    · rcases newBlock_frame_at run row with oldRow | rfl
      · exact closed.edges block oldBlock term member edge edgeMember destination oldRow entry entryMember permitted
      · have fresh := paramIds_lower_bound (List.of_mem_zip entryMember).1
        have old := oldBound entry.1.1 permitted
        exact (Nat.not_lt_of_ge fresh old).elim
    · simp at member


#print axioms WritableClosed.emitDef_preserve
#print axioms writableClosed_fresh_definition
#print axioms WritableClosed.emitDef_extend
#print axioms WritableClosed.newBlock_preserve

end Goose.Lower.Validation

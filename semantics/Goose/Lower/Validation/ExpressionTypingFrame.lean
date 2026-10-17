import Goose.Lower.Validation.ExpressionTypingAuthority
import Goose.Lower.Validation.DenseDefinitions
import Goose.Lower.Validation.ValueTypes

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def permissionFunc (le : LEnv) (state : LS) : Func :=
  { name := "", params := [], results := [], slots := le.slots, scopes := #[],
    blocks := state.blocks.map fun block => ⟨block.params, block.insts.toList⟩,
    summary := .unknown, org := none }

theorem tyEnv_contentsWritable (le : LEnv) (state : LS) (value : ValueId) :
    (tyEnv le state).contentsWritable value =
      ((permissionFunc le state).permissionsFromTables (le.globals.map (·.2)) le.mod.structs state.vals)[value]?.map (·.2) := rfl

theorem permissionFunc_definitions (le : LEnv) (state : LS) :
    (permissionFunc le state).blocks.toList.flatMap GIR.Block.defs = state.defs := by
  simp only [permissionFunc, LS.defs, GIR.Block.defs, Array.toList_map, List.flatMap_map]
  rfl

theorem permissionFunc_numValues {state : LS} (checked : state.DenseDefinitions) (le : LEnv) :
    (permissionFunc le state).numValues = state.vals.size := by
  rw [Func.numValues_eq_definition_count, permissionFunc_definitions, checked.length]

theorem permissionFunc_param_bound {state : LS} (checked : state.DenseDefinitions) {le : LEnv}
    {block : GIR.Block} (member : block ∈ (permissionFunc le state).blocks.toList)
    {param : ValueId × VTy} (row : param ∈ block.params) : param.1 < state.vals.size := by
  apply checked.mem_lt
  rw [← permissionFunc_definitions le state]
  apply List.mem_flatMap.mpr
  refine ⟨block, member, ?_⟩
  simp only [GIR.Block.defs, List.mem_append, List.mem_map]
  exact Or.inl ⟨param, row, rfl⟩

theorem permissionFunc_def_bound {state : LS} (checked : state.DenseDefinitions) {le : LEnv}
    {block : GIR.Block} (member : block ∈ (permissionFunc le state).blocks.toList)
    {value : ValueId} {op : Op} (row : Inst.def value op ∈ block.insts) : value < state.vals.size := by
  apply checked.mem_lt
  rw [← permissionFunc_definitions le state]
  apply List.mem_flatMap.mpr
  refine ⟨block, member, ?_⟩
  simp only [GIR.Block.defs, List.mem_append]
  apply Or.inr
  apply List.mem_filterMap.mpr
  exact ⟨.def value op, row, rfl⟩

theorem list_mem_modify_cases {α : Type} (values : List α) (index : Nat) (modify : α → α)
    {value : α} (member : value ∈ values.modify index modify) :
    value ∈ values ∨ ∃ old, old ∈ values ∧ value = modify old := by
  induction values generalizing index with
  | nil => simp at member
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.modify_zero_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact Or.inr ⟨head, by simp, rfl⟩
      · exact Or.inl (by simp [member])
    | succ index =>
      simp only [List.modify_succ_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact Or.inl (by simp)
      · rcases ih index member with old | ⟨old, belongs, shape⟩
        · exact Or.inl (by simp [old])
        · exact Or.inr ⟨old, by simp [belongs], shape⟩

theorem emitDef_frame_blocks {le : LEnv} {before after : LS} {value : ValueId} {op : Op}
    {current : BlockId} (live : before.cur = some current)
    (run : emitDef op le before = (value, after))
    {block : GIR.Block} (member : block ∈ (permissionFunc le after).blocks.toList) :
    ∃ old, old ∈ (permissionFunc le before).blocks.toList ∧ block.params = old.params ∧
      (block.insts = old.insts ∨ block.insts = old.insts ++ [.def before.vals.size op]) := by
  rw [emitDef_run op le live] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  simp only [permissionFunc, Array.toList_map, Array.toList_modify, List.mem_map] at member
  obtain ⟨actual, member, rfl⟩ := member
  rcases list_mem_modify_cases _ _ _ member with unchanged | ⟨old, oldMember, shape⟩
  · refine ⟨⟨actual.params, actual.insts.toList⟩, ?_, rfl, Or.inl rfl⟩
    simp only [permissionFunc, Array.toList_map, List.mem_map]
    exact ⟨actual, unchanged, rfl⟩
  · subst actual
    refine ⟨⟨old.params, old.insts.toList⟩, ?_, rfl, Or.inr ?_⟩
    · simp only [permissionFunc, Array.toList_map, List.mem_map]
      exact ⟨old, oldMember, rfl⟩
    · simp

theorem emitDef_frame_param_bound {le : LEnv} {before after : LS} {value : ValueId} {op : Op}
    {current : BlockId} (checked : before.DenseDefinitions) (live : before.cur = some current)
    (run : emitDef op le before = (value, after))
    {block : GIR.Block} (member : block ∈ (permissionFunc le after).blocks.toList)
    {param : ValueId × VTy} (row : param ∈ block.params) : param.1 < before.vals.size := by
  obtain ⟨old, oldMember, sameParams, _⟩ := emitDef_frame_blocks live run member
  have oldRow : param ∈ old.params := by rw [← sameParams]; exact row
  exact permissionFunc_param_bound checked oldMember oldRow

theorem emitDef_frame_fresh_operation {le : LEnv} {before after : LS} {value : ValueId} {op : Op}
    {current : BlockId} (checked : before.DenseDefinitions) (live : before.cur = some current)
    (run : emitDef op le before = (value, after))
    {block : GIR.Block} (member : block ∈ (permissionFunc le after).blocks.toList)
    {actual : Op} (row : Inst.def before.vals.size actual ∈ block.insts) : actual = op := by
  obtain ⟨old, oldMember, _, sameInsts⟩ := emitDef_frame_blocks live run member
  rcases sameInsts with same | same
  · rw [same] at row
    have impossible := permissionFunc_def_bound checked oldMember row
    exact (Nat.lt_irrefl _ impossible).elim
  · rw [same, List.mem_append, List.mem_singleton] at row
    rcases row with oldRow | sameDef
    · have impossible := permissionFunc_def_bound checked oldMember oldRow
      exact (Nat.lt_irrefl _ impossible).elim
    · exact (Inst.def.inj sameDef).2

theorem emitDef_fresh_size {le : LEnv} {before after : LS} {value : ValueId} {op : Op}
    {current : BlockId} (live : before.cur = some current) (run : emitDef op le before = (value, after)) :
    value = before.vals.size ∧ after.vals.size = before.vals.size + 1 := by
  rw [emitDef_run op le live] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  exact ⟨rfl, by simp⟩

theorem contentsClosed_fresh_definition {le : LEnv} {before after : LS} {value : ValueId} {op : Op}
    {current : BlockId} (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef op le before = (value, after))
    (operation : ContentsOperation (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals (fun candidate => candidate = value) value op) :
    ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals (fun candidate => candidate = value) := by
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

theorem ContentsClosed.tyEnv_contents {le : LEnv} {state : LS} {authorized : ValueId → Prop}
    (closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le state) state.vals authorized) {value : ValueId} (member : authorized value) :
    (tyEnv le state).contentsWritable value = some true := by
  rw [tyEnv_contentsWritable]
  have checked := closed.permissions value member
  cases row : ((permissionFunc le state).permissionsFromTables (le.globals.map (·.2)) le.mod.structs state.vals)[value]? with
  | none => simp [permissionsAt, row] at checked
  | some cap =>
    simp only [permissionsAt, row, Option.getD_some] at checked
    simp only [Option.map_some, checked]

theorem emitDef_slot_contents {le : LEnv} {before after : LS} {value : ValueId} {slot : SlotId}
    {descriptor : Slot} {current : BlockId} (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (row : le.slots[slot]? = some descriptor)
    (run : emitDef (.slotAddr slot) le before = (value, after)) :
    (tyEnv le after).contentsWritable value = some true := by
  have closed := contentsClosed_fresh_definition checked bounded live run ⟨descriptor, row⟩
  exact closed.tyEnv_contents rfl

theorem emitDef_global_contents {le : LEnv} {before after : LS} {value : ValueId} {global : GlobalId}
    {ty : Ty} {kind : VarKind} {current : BlockId} (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (row : le.globals[global]? = some (ty, kind))
    (run : emitDef (.globalAddr global) le before = (value, after)) :
    (tyEnv le after).contentsWritable value = some true := by
  have operation : ContentsOperation (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals (fun candidate => candidate = value) value (.globalAddr global) := by
    exact ⟨kind, by simp [Array.getElem?_map, row]⟩
  exact (contentsClosed_fresh_definition checked bounded live run operation).tyEnv_contents rfl

theorem typedPermissions_retained {before after : LS} (extension : TypePrefix before after)
    {value : ValueId} (typed : (typedPermissions before.vals value).2 = true) :
    (typedPermissions after.vals value).2 = true := by
  cases row : before.vals[value]? with
  | none => simp [typedPermissions, row] at typed
  | some cell =>
    cases cell with
    | none => simp [typedPermissions, row] at typed
    | some ty =>
      have recorded := extension value ty row
      simpa only [typedPermissions, row, recorded] using typed

theorem ContentsOperation.retained {le : LEnv} {before after : LS} {authorized : ValueId → Prop}
    {value : ValueId} {op : Op} (extension : TypePrefix before after)
    (operation : ContentsOperation (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized value op) :
    ContentsOperation (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized value op := by
  cases op with
  | slotAddr _ | globalAddr _ => exact operation
  | refFreeze _ => contradiction
  | fieldAddr owner index =>
    obtain ⟨member, mu, id, fields, descriptor, field, typed, descriptorRow, fieldRow, writable⟩ := operation
    exact ⟨member, mu, id, fields, descriptor, field, extension owner _ typed, descriptorRow, fieldRow, writable⟩
  | snapshot _ _ | refElem _ _ | indexChecked _ _ _ | indexProven _ _ => exact operation
  | _ => exact typedPermissions_retained extension operation

theorem emitDef_frame_at {le : LEnv} {before after : LS} {value : ValueId} {op : Op}
    {current target : BlockId} (live : before.cur = some current)
    (run : emitDef op le before = (value, after)) {block : GIR.Block}
    (row : (permissionFunc le after).blocks[target]? = some block) :
    ∃ old, (permissionFunc le before).blocks[target]? = some old ∧ block.params = old.params := by
  rw [emitDef_run op le live] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  simp only [permissionFunc, Array.getElem?_map, Array.getElem?_modify] at row ⊢
  by_cases same : current = target
  · simp only [same, ↓reduceIte] at row
    cases previous : before.blocks[target]? with
    | none => simp [previous] at row
    | some old =>
      simp only [previous, Option.map_some, Option.some.injEq] at row
      subst block
      exact ⟨⟨old.params, old.insts.toList⟩, by simp, rfl⟩
  · simp only [same, ↓reduceIte] at row
    cases previous : before.blocks[target]? with
    | none => simp [previous] at row
    | some old =>
      simp only [previous, Option.map_some, Option.some.injEq] at row
      subst block
      exact ⟨⟨old.params, old.insts.toList⟩, by simp, rfl⟩

theorem ContentsClosed.emitDef_preserve {le : LEnv} {before after : LS}
    {value : ValueId} {op : Op} {current : BlockId} {authorized : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef op le before = (value, after))
    (closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized) :
    ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized := by
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
    exact typedPermissions_retained extension (closed.entry old oldRow param oldMember permitted)
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

theorem ContentsOperation.mono {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {types : Array (Option VTy)} {first second : ValueId → Prop}
    {value : ValueId} {op : Op} (inclusion : ∀ candidate, first candidate → second candidate)
    (operation : ContentsOperation globalKinds structs func types first value op) :
    ContentsOperation globalKinds structs func types second value op := by
  cases op with
  | fieldAddr owner index => exact ⟨inclusion owner operation.1, operation.2⟩
  | snapshot _ owner | refElem owner _ | indexChecked owner _ _ | indexProven owner _ =>
    exact inclusion owner operation
  | _ => exact operation

theorem ContentsClosed.union {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {types : Array (Option VTy)} {first second : ValueId → Prop}
    (left : ContentsClosed globalKinds structs func types first)
    (right : ContentsClosed globalKinds structs func types second) :
    ContentsClosed globalKinds structs func types (fun value => first value ∨ second value) := by
  constructor
  · intro value member
    exact member.elim (left.bounded value) (right.bounded value)
  · intro block row param member permitted
    exact permitted.elim (left.entry block row param member) (right.entry block row param member)
  · intro block blockMember value op member permitted
    rcases permitted with permitted | permitted
    · exact (left.definitions block blockMember value op member permitted).mono (fun _ => Or.inl)
    · exact (right.definitions block blockMember value op member permitted).mono (fun _ => Or.inr)
  · intro block blockMember term member edge edgeMember destination row entry entryMember permitted
    rcases permitted with permitted | permitted
    · exact Or.inl (left.edges block blockMember term member edge edgeMember destination row entry entryMember permitted)
    · exact Or.inr (right.edges block blockMember term member edge edgeMember destination row entry entryMember permitted)

theorem ContentsClosed.emitDef_extend {le : LEnv} {before after : LS}
    {value : ValueId} {op : Op} {current : BlockId} {authorized : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef op le before = (value, after))
    (closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized)
    (operation : ContentsOperation (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals (fun candidate => authorized candidate ∨ candidate = value) value op) :
    ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals (fun candidate => authorized candidate ∨ candidate = value) := by
  have retained := closed.emitDef_preserve checked bounded live run
  have afterDense := (dense_emitDef op le before value after run checked bounded).1
  obtain ⟨fresh, size⟩ := emitDef_fresh_size live run
  constructor
  · intro candidate member
    rcases member with member | rfl
    · exact retained.bounded candidate member
    · rw [permissionFunc_numValues afterDense le, fresh, size]
      exact Nat.lt_succ_self _
  · intro block row param member permitted
    rcases permitted with permitted | permitted
    · exact retained.entry block row param member permitted
    · have bound := emitDef_frame_param_bound checked live run
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? row)) member
      rw [permitted, fresh] at bound
      exact (Nat.lt_irrefl _ bound).elim
  · intro block blockMember result actual member permitted
    rcases permitted with permitted | rfl
    · exact (retained.definitions block blockMember result actual member permitted).mono (fun _ => Or.inl)
    · have same : actual = op := by
        apply emitDef_frame_fresh_operation checked live run blockMember
        simpa only [← fresh] using member
      subst actual
      exact operation
  · intro block blockMember term member edge edgeMember destination row entry entryMember permitted
    rcases permitted with permitted | permitted
    · exact Or.inl (retained.edges block blockMember term member edge edgeMember destination row entry entryMember permitted)
    · have bound := emitDef_frame_param_bound checked live run
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? row)) (List.of_mem_zip entryMember).1
      rw [permitted, fresh] at bound
      exact (Nat.lt_irrefl _ bound).elim

#print axioms ContentsClosed.emitDef_preserve
#print axioms ContentsClosed.emitDef_extend
#print axioms emitDef_slot_contents

end Goose.Lower.Validation

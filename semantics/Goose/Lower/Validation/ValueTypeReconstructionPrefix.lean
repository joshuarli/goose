import Goose.Lower.Validation.ValueTypeReconstructionPermissionExtension
import Goose.Lower.Validation.DenseDefinitions
import Goose.Lower.Sim
import Goose.Lower.Validation.ExpressionTypingFrame

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem permissionEdge_argument_uses {term : Term} {edge : BlockId × List ValueId}
    (member : edge ∈ term.permissionEdges) {argument : ValueId} (used : argument ∈ edge.2) :
    argument ∈ term.uses := by
  cases term with
  | br target args =>
    simp only [Term.permissionEdges, List.mem_singleton] at member
    subst edge
    exact used
  | condbr condition trueBlock trueArgs falseBlock falseArgs =>
    simp only [Term.permissionEdges, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same <;> subst edge <;> simp [Term.uses, used]
  | _ => simp [Term.permissionEdges] at member

theorem permissionGraphExtension_of_prefix
    {le : LEnv} {state : LS} {func : Func}
    (dense : state.DenseDefinitions) (extension : ExtT state func.blocks)
    (slots : le.slots = func.slots)
    (operands : ∀ inst ∈ state.insts, ∀ value ∈ inst.uses, value < state.vals.size) :
    PermissionGraphExtension (permissionFunc le state) func := by
  have numValues := permissionFunc_numValues dense le
  have oldBlock : ∀ (index : BlockId) (block : GIR.Block),
      (permissionFunc le state).blocks[index]? = some block →
      ∃ builder : BlockB, state.blocks[index]? = some builder ∧
        block = ⟨builder.params, builder.insts.toList⟩ := by
    intro index block row
    change (state.blocks.map fun block => GIR.Block.mk block.params block.insts.toList)[index]? = some block at row
    rw [Array.getElem?_map] at row
    cases builderRow : state.blocks[index]? with
    | none => simp [builderRow] at row
    | some builder =>
      simp only [builderRow, Option.map_some, Option.some.injEq] at row
      exact ⟨builder, rfl, row.symm⟩
  constructor
  · exact slots
  · intro index block row
    obtain ⟨builder, builderRow, rfl⟩ := oldBlock index block row
    obtain ⟨next, nextRow, parameters, suffix, instructions⟩ := extension.2 index builder builderRow
    exact ⟨next, nextRow, parameters, fun inst member => by rw [instructions]; exact List.mem_append_left _ member⟩
  · intro block member value op definition operand used
    obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    obtain ⟨builder, builderRow, rfl⟩ := oldBlock index block row
    rw [numValues]
    exact operands (.def value op) (List.mem_flatMap.mpr
      ⟨builder, Array.mem_toList_iff.mpr (Array.mem_of_getElem? builderRow), definition⟩) operand used
  · intro block member term definition edge edgeMember argument used
    obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    obtain ⟨builder, builderRow, rfl⟩ := oldBlock index block row
    rw [numValues]
    exact operands (.term term) (List.mem_flatMap.mpr
      ⟨builder, Array.mem_toList_iff.mpr (Array.mem_of_getElem? builderRow), definition⟩)
      argument (permissionEdge_argument_uses edgeMember used)

theorem permissionContents_eq_false_of_option
    {caps : Array (Bool × Bool)} {value : ValueId}
    (readonly : caps[value]?.map (·.2) = some false) :
    (permissionsAt caps value).2 = false := by
  cases row : caps[value]? with
  | none => simp [row] at readonly
  | some capability =>
    simpa only [row, Option.map_some, Option.some.injEq, permissionsAt,
      Option.getD_some] using readonly

theorem permissionContents_option_false
    {caps : Array (Bool × Bool)} {value : ValueId} (bound : value < caps.size)
    (readonly : (permissionsAt caps value).2 = false) :
    caps[value]?.map (·.2) = some false := by
  cases row : caps[value]? with
  | none => exact (Nat.not_le_of_gt bound (Array.getElem?_eq_none_iff.mp row)).elim
  | some capability =>
    simp only [permissionsAt, row, Option.getD_some] at readonly
    simp only [Option.map_some, readonly]

theorem readonly_snapshot_contents_retained
    {le : LEnv} {state : LS} {func : Func} {module : GIR.Module}
    (dense : state.DenseDefinitions) (extension : ExtT state func.blocks)
    (slots : le.slots = func.slots)
    (globals : module.globals.map (·.kind) = le.globals.map (·.2))
    (structs : module.structs = le.mod.structs)
    (operands : ∀ inst ∈ state.insts, ∀ value ∈ inst.uses, value < state.vals.size)
    {newTypes : Array (Option VTy)}
    (prefixTypes : ∀ value, value < state.vals.size → state.vals[value]? = newTypes[value]?)
    {owner : ValueId} (oldBound : owner < state.vals.size) (newBound : owner < func.numValues)
    (readonly : (tyEnv le state).contentsWritable owner = some false) :
    (func.permissions module newTypes)[owner]?.map (·.2) = some false := by
  have graph := permissionGraphExtension_of_prefix dense extension slots operands
  have oldReadOnly :
      (permissionsAt ((permissionFunc le state).permissionsFromTables
        (le.globals.map (·.2)) le.mod.structs state.vals) owner).2 = false := by
    rw [tyEnv_contentsWritable] at readonly
    exact permissionContents_eq_false_of_option readonly
  have retained := permissionsFromTables_contents_antitone graph
    (fun value bound => prefixTypes value (by rwa [permissionFunc_numValues dense le] at bound))
    (by rwa [permissionFunc_numValues dense le]) oldReadOnly
  apply permissionContents_option_false
  · simpa only [Func.permissions, permissionsFromTables_size] using newBound
  · simpa only [Func.permissions, globals, structs] using retained

theorem tyEnv_contentsWritable_present (le : LEnv) {state : LS}
    (dense : state.DenseDefinitions) {value : ValueId} (bound : value < state.vals.size) :
    ∃ writable, (tyEnv le state).contentsWritable value = some writable := by
  rw [tyEnv_contentsWritable]
  have permissionBound : value < ((permissionFunc le state).permissionsFromTables
      (le.globals.map (·.2)) le.mod.structs state.vals).size := by
    rwa [permissionsFromTables_size, permissionFunc_numValues dense le]
  cases row : ((permissionFunc le state).permissionsFromTables
      (le.globals.map (·.2)) le.mod.structs state.vals)[value]? with
  | none => exact (Nat.not_le_of_gt permissionBound (Array.getElem?_eq_none_iff.mp row)).elim
  | some capability => exact ⟨capability.2, rfl⟩

theorem permissionContents_option_true {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {types : Array (Option VTy)} {authorized : ValueId → Prop}
    (closed : ContentsClosed globalKinds structs func types authorized)
    {value : ValueId} (member : authorized value) :
    (func.permissionsFromTables globalKinds structs types)[value]?.map (·.2) = some true := by
  have present := closed.permissions value member
  have bound := closed.permissions.bound member
  cases row : (func.permissionsFromTables globalKinds structs types)[value]? with
  | none => exact (Nat.not_le_of_gt bound (Array.getElem?_eq_none_iff.mp row)).elim
  | some capability =>
    simp only [permissionsAt, row, Option.getD_some] at present
    simp only [Option.map_some, present]

end Goose.Lower.Validation

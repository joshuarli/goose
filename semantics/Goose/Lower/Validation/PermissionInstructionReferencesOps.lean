import Goose.Lower.Validation.PermissionPreservationNewEmit
import Goose.Lower.Validation.PermissionPreservationInstructionRules

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def PermissionFreeOperation : Op → Prop
  | .ownerBorrow _ | .snapshot .. | .call .. | .push .. | .pop .. => False
  | _ => True

theorem FreshPermissionInstruction.freeOperation {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {state : LS} {value : ValueId} {op : Op} (free : PermissionFreeOperation op) :
    FreshPermissionInstruction module func le first state (.def value op) := by
  cases op <;> simp only [PermissionFreeOperation] at free
  all_goals first | contradiction | skip
  all_goals
    constructor
    · constructor
      · intro a b c impossible; cases impossible
      · intro a b c d e impossible; cases impossible
      · intro owner mutation; cases mutation
      · intro a b impossible; cases impossible
      · intro a b c impossible; cases impossible
      · intro a b c d impossible; cases impossible
      · intro a b c d e impossible; cases impossible
      · intro a b c d impossible; cases impossible
      · intro a b impossible; cases impossible
    · constructor
      · intro a b c impossible; cases impossible
      · intro a b c impossible; cases impossible

theorem newPermissions_free_emitDef {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {value : ValueId} {op : Op}
    (free : PermissionFreeOperation op) (run : emitDef op le before = (value, after)) :
    NewPermissionInstructions module func le first before after :=
  .emitDef run (fun _ => .freeOperation free)

theorem newPermissions_freezeTo {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {value result : ValueId} {mu : Mutability}
    (run : freezeTo mu value le before = (result, after)) :
    NewPermissionInstructions module func le first before after := by
  rcases freezeTo_cases run with ⟨_, rfl⟩ | emitted
  · exact .of_blocks_eq rfl
  · exact newPermissions_free_emitDef (by trivial) emitted

theorem newPermissions_coerceTo {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {value result : ValueId} {target : Ty} {origin : OriginId}
    (run : coerceTo target value origin le before = (result, after)) :
    NewPermissionInstructions module func le first before after := by
  rcases coerceTo_cases run with ⟨_, rfl⟩ | ⟨_, _, emitted⟩ | ⟨_, view, middle, _, firstRun, lastRun⟩
  · exact .of_blocks_eq rfl
  · exact newPermissions_free_emitDef (by trivial) emitted
  · intro instruction member
    rcases newPermissions_free_emitDef (module := module) (func := func) (first := first)
        (by trivial) lastRun instruction member with old | issued
    · cases current : before.cur with
      | none =>
        rw [emitDef_none _ _ current] at firstRun
        obtain ⟨_, rfl⟩ := Prod.mk.inj firstRun
        exact Or.inl old
      | some block =>
        rw [emitDef_run _ _ current] at firstRun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj firstRun
        rcases permission_appendInst_membership old with original | same
        · exact Or.inl original
        · subst instruction
          exact Or.inr (.freeOperation trivial)
    · exact Or.inr issued

theorem newPermissions_coerceSlot {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {value result : ValueId} {slot : SlotId} {origin : OriginId}
    (run : coerceSlot slot value origin le before = (result, after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [coerceSlot, bind_run, read_apply] at run
  cases row : le.slots[slot]? with
  | none =>
    simp only [row, pure_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact .of_blocks_eq rfl
  | some destination =>
    simp only [row] at run
    exact newPermissions_coerceTo run

theorem newPermissions_coerceResult {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {value result : ValueId} {origin : OriginId}
    (run : coerceResult value origin le before = (result, after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [coerceResult, bind_run, read_apply] at run
  cases row : le.results.head? with
  | none =>
    simp only [row, pure_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact .of_blocks_eq rfl
  | some destination =>
    simp only [row] at run
    exact newPermissions_coerceTo run

theorem permissionTransfer_coerceTo {profile : ArtifactProfile} {le : LEnv} {first : Nat}
    {before after : LS} {value result : ValueId} {target : Ty} {origin : OriginId}
    (transfer : PermissionTransfer profile (FreshWritableEvidence le first before)
      (FreshContentsEvidence le first before) value target)
    (run : coerceTo target value origin le before = (result, after)) :
    PermissionTransfer profile (FreshWritableEvidence le first after)
      (FreshContentsEvidence le first after) result target := by
  cases target with
  | ref mu referent =>
    cases mu with
    | readOnly => trivial
    | mutable =>
      rcases coerceTo_cases run with ⟨rfl, rfl⟩ | ⟨_, impossible, _⟩ | ⟨_, _, _, impossible, _, _⟩
      · exact transfer
      · cases impossible
      · cases impossible
  | _ => trivial

theorem permissionTransfer_coerceSlot {profile : ArtifactProfile} {le : LEnv} {first : Nat}
    {before after : LS} {value result : ValueId} {slot : SlotId} {origin : OriginId}
    {destination : GIR.Slot}
    (row : le.slots[slot]? = some destination)
    (transfer : PermissionTransfer profile (FreshWritableEvidence le first before)
      (FreshContentsEvidence le first before) value destination.ty)
    (run : coerceSlot slot value origin le before = (result, after)) :
    PermissionTransfer profile (FreshWritableEvidence le first after)
      (FreshContentsEvidence le first after) result destination.ty := by
  simp only [coerceSlot, bind_run, read_apply, row] at run
  exact permissionTransfer_coerceTo transfer run

theorem permissionTransfer_coerceResult {profile : ArtifactProfile} {le : LEnv} {first : Nat}
    {before after : LS} {value result : ValueId} {target : Ty} {origin : OriginId}
    (row : le.results.head? = some target)
    (transfer : PermissionTransfer profile (FreshWritableEvidence le first before)
      (FreshContentsEvidence le first before) value target)
    (run : coerceResult value origin le before = (result, after)) :
    PermissionTransfer profile (FreshWritableEvidence le first after)
      (FreshContentsEvidence le first after) result target := by
  simp only [coerceResult, bind_run, read_apply, row] at run
  exact permissionTransfer_coerceTo transfer run

#print axioms newPermissions_coerceTo
#print axioms permissionTransfer_coerceTo

end Goose.Lower.Validation

import Goose.Lower.Validation.PermissionPreservationPatch
import Goose.Lower.Validation.JoinContentsAllocation

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem WritableClosed.patchBrs {le : LEnv} {before after : LS} {result : Unit}
    {target : BlockId} (incoming : List (BlockId × ValueId)) {authorized contents : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : patchBrs target incoming le before = (result, after))
    (closed : WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized contents)
    (arguments : ∀ pair ∈ incoming, authorized pair.2) :
    WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized contents := by
  induction incoming generalizing before after result with
  | nil =>
      obtain ⟨_, rfl⟩ := pure_eq.mp run
      exact closed
  | cons pair rest ih =>
      obtain ⟨unit, middle, firstRun, restRun⟩ := bind_eq.mp run
      have middleDense := dense_patchTerm pair.1 (.br target [pair.2]) le before unit middle firstRun checked bounded
      apply ih middleDense.1 middleDense.2.1 restRun
      · apply closed.patchTerm checked bounded firstRun
        intro edge member destination row entry belongs permitted
        have edgeEqual : edge = (target, [pair.2]) := by simpa [Term.permissionEdges] using member
        subst edge
        have same : entry.2 = pair.2 := by simpa using (List.of_mem_zip belongs).2
        rw [same]
        exact arguments pair (List.mem_cons_self ..)
      · intro next member
        exact arguments next (List.mem_cons_of_mem _ member)

theorem joinBinding_newBlock_fresh {le : LEnv} {before after : LS} {types : List VTy}
    {result : BlockId × List ValueId} {contents : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (targets : TargetsBounded before) (nonempty : 0 < before.blocks.size)
    (run : newBlock types le before = (result, after)) :
    WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals
      (fun candidate => before.vals.size ≤ candidate ∧ candidate < after.vals.size) contents := by
  have afterDense := (dense_newBlock types le before result after run checked bounded).1
  constructor
  · intro value member
    rw [permissionFunc_numValues afterDense le]
    exact member.2
  · intro block row param member permitted
    rw [newBlock_frame_old_at run nonempty] at row
    have old := permissionFunc_param_bound checked
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? row)) member
    exact (Nat.not_lt_of_ge permitted.1 old).elim
  · intro block blockMember value op member permitted
    rcases newBlock_frame_blocks run blockMember with oldBlock | rfl
    · have old := permissionFunc_def_bound checked oldBlock member
      exact (Nat.not_lt_of_ge permitted.1 old).elim
    · simp at member
  · intro block blockMember term member edge edgeMember destination row entry entryMember permitted
    rcases newBlock_frame_blocks run blockMember with oldBlock | rfl
    · have targetBound := permissionFunc_target_bound targets oldBlock member edgeMember
      rw [newBlock_frame_old_at run targetBound] at row
      have old := permissionFunc_param_bound checked
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? row)) (List.of_mem_zip entryMember).1
      exact (Nat.not_lt_of_ge permitted.1 old).elim
    · simp at member


theorem WritableClosed.newJoin {le : LEnv} {before after : LS} {ty : VTy}
    {result : BlockId × List ValueId} {authorized contents : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (targets : TargetsBounded before) (nonempty : 0 < before.blocks.size)
    (run : newBlock [ty] le before = (result, after))
    (closed : WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized contents) :
    WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals
      (fun value => authorized value ∨ value = before.vals.size) contents := by
  have fresh := joinBinding_newBlock_fresh (contents := contents) checked bounded targets nonempty run
  have size : after.vals.size = before.vals.size + 1 := by
    rw [newBlock1_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    simp
  have predicates : (fun value => before.vals.size ≤ value ∧ value < after.vals.size) =
      (fun value => value = before.vals.size) := by
    funext value
    apply propext
    rw [size]
    omega
  rw [predicates] at fresh
  exact (closed.newBlock_preserve checked bounded run).union fresh

theorem WritableClosed.empty (globalKinds : Array VarKind) (structs : Array StructDef)
    (func : Func) (types : Array (Option VTy)) (contents : ValueId → Prop) :
    WritableClosed globalKinds structs func types (fun _ => False) contents := by
  constructor <;> simp

theorem FreshWritableEvidence.common {le : LEnv} {first : Nat} {state : LS}
    (incoming : List (BlockId × ValueId))
    (evidence : ∀ pair ∈ incoming, FreshWritableEvidence le first state pair.2) :
    ∃ writable contents,
      WritableClosed (le.globals.map (·.2)) le.mod.structs
        (permissionFunc le state) state.vals writable contents ∧
      ContentsClosed (le.globals.map (·.2)) le.mod.structs
        (permissionFunc le state) state.vals contents ∧
      NonIntegerParameters (permissionFunc le state) writable ∧
      NonIntegerParameters (permissionFunc le state) contents ∧
      (∀ pair ∈ incoming, writable pair.2) ∧
      (∀ value, writable value → first ≤ value) ∧
      (∀ value, contents value → first ≤ value) := by
  induction incoming with
  | nil =>
    exact ⟨fun _ => False, fun _ => False, .empty _ _ _ _ _, .empty _ _ _ _,
      .empty _, .empty _, by simp, by simp, by simp⟩
  | cons pair rest ih =>
    obtain ⟨leftW, leftC, leftBindings, leftElements, leftWparams, leftCparams, leftMember, leftFreshW, leftFreshC⟩ :=
      evidence pair (by simp)
    obtain ⟨rightW, rightC, rightBindings, rightElements, rightWparams, rightCparams, rightMembers, rightFreshW, rightFreshC⟩ :=
      ih (fun next member => evidence next (List.mem_cons_of_mem _ member))
    refine ⟨fun value => leftW value ∨ rightW value, fun value => leftC value ∨ rightC value,
      (leftBindings.monoContents (fun _ member => Or.inl member)).union
        (rightBindings.monoContents (fun _ member => Or.inr member)),
      leftElements.union rightElements, leftWparams.union rightWparams, leftCparams.union rightCparams,
      ?_, ?_, ?_⟩
    · intro next member
      rcases List.mem_cons.mp member with rfl | member
      · exact Or.inl leftMember
      · exact Or.inr (rightMembers next member)
    · intro value member
      exact member.elim (leftFreshW value) (rightFreshW value)
    · intro value member
      exact member.elim (leftFreshC value) (rightFreshC value)

#print axioms WritableClosed.patchBrs
#print axioms WritableClosed.newJoin
#print axioms FreshWritableEvidence.common

end Goose.Lower.Validation

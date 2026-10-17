import Goose.Lower.Validation.JoinContentsGraph
import Goose.Lower.Validation.Typing

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem joinContents_newBlock_fresh {le : LEnv} {before after : LS} {types : List VTy}
    {result : BlockId × List ValueId}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (targets : TargetsBounded before) (nonempty : 0 < before.blocks.size)
    (run : newBlock types le before = (result, after)) :
    ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals
      (fun candidate => before.vals.size ≤ candidate ∧ candidate < after.vals.size) := by
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


theorem ContentsClosed.newJoin {le : LEnv} {before after : LS} {ty : VTy}
    {result : BlockId × List ValueId} {authorized : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (targets : TargetsBounded before) (nonempty : 0 < before.blocks.size)
    (run : newBlock [ty] le before = (result, after))
    (closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized) :
    ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals
      (fun value => authorized value ∨ value = before.vals.size) := by
  have fresh := joinContents_newBlock_fresh checked bounded targets nonempty run
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

theorem NonIntegerParameters.newJoin {le : LEnv} {before after : LS} {ty : VTy}
    {result : BlockId × List ValueId} {authorized : ValueId → Prop}
    (checked : before.DenseDefinitions)
    (run : newBlock [ty] le before = (result, after))
    (oldBound : ∀ value, authorized value → value < before.vals.size)
    (old : NonIntegerParameters (permissionFunc le before) authorized)
    (noninteger : ∀ intTy, ty ≠ .data (.int intTy)) :
    NonIntegerParameters (permissionFunc le after)
      (fun value => authorized value ∨ value = before.vals.size) := by
  have fresh := nonIntegerParameters_newBlock_fresh run checked (by simpa using noninteger)
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
  exact (old.newBlock_preserve run oldBound).union fresh

end Goose.Lower.Validation

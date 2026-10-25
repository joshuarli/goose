import Goose.Lower.Validation.PermissionPreservationFrame
import Goose.Lower.Validation.ExpressionTypingEdges

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem writableClosed_newBlock_fresh {le : LEnv} {before after : LS} {types : List VTy}
    {result : BlockId × List ValueId} {current : BlockId} {contents : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (targets : TargetsBounded before) (live : before.cur = some current)
    (run : newBlock types le before = (result, after)) :
    WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals
      (fun candidate => before.vals.size ≤ candidate ∧ candidate < after.vals.size) contents := by
  have afterDense := (dense_newBlock types le before result after run checked bounded).1
  have nonempty : 0 < before.blocks.size := Nat.zero_lt_of_lt (bounded current live)
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


theorem WritableClosed.emitTerm {le : LEnv} {before after : LS}
    {result : Unit} {term : Term} {current : BlockId} {authorized contents : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitTerm term le before = (result, after))
    (closed : WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized contents)
    (edges : ∀ edge ∈ term.permissionEdges, ∀ destination,
      (permissionFunc le before).blocks[edge.1]? = some destination →
      ∀ entry ∈ destination.params.zip edge.2, authorized entry.1.1 → authorized entry.2) :
    WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized contents := by
  have sameVals : after.vals = before.vals := by
    rw [emitTerm_run term le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    rfl
  have afterDense := (dense_emitTerm term le before result after run checked bounded).1
  constructor
  · intro value member
    rw [permissionFunc_numValues afterDense le, sameVals]
    simpa only [permissionFunc_numValues checked le] using closed.bounded value member
  · intro block row param member permitted
    obtain ⟨old, oldRow, params⟩ := emitTerm_frame_at live run row
    rw [sameVals]
    exact closed.entry old oldRow param (by rw [← params]; exact member) permitted
  · intro block blockMember value op member permitted
    obtain ⟨old, oldMember, _, instructions⟩ := emitTerm_frame_blocks live run blockMember
    have oldInstruction : Inst.def value op ∈ old.insts := by
      rcases instructions with same | same
      · rw [same] at member; exact member
      · rw [same, List.mem_append, List.mem_singleton] at member
        rcases member with member | impossible
        · exact member
        · cases impossible
    exact (closed.definitions old oldMember value op oldInstruction permitted).retained
      (types_emitTerm term le before result after run)
  · intro block blockMember actual member edge edgeMember destination row entry entryMember permitted
    obtain ⟨old, oldMember, _, instructions⟩ := emitTerm_frame_blocks live run blockMember
    obtain ⟨oldDestination, oldRow, params⟩ := emitTerm_frame_at live run row
    have oldEntry : entry ∈ oldDestination.params.zip edge.2 := by rw [← params]; exact entryMember
    rcases instructions with same | same
    · rw [same] at member
      exact closed.edges old oldMember actual member edge edgeMember oldDestination oldRow entry oldEntry permitted
    · rw [same, List.mem_append, List.mem_singleton] at member
      rcases member with oldInstruction | equation
      · exact closed.edges old oldMember actual oldInstruction edge edgeMember oldDestination oldRow entry oldEntry permitted
      · have sameTerm := Inst.term.inj equation
        subst actual
        exact edges edge edgeMember oldDestination oldRow entry oldEntry permitted


#print axioms writableClosed_newBlock_fresh
#print axioms WritableClosed.emitTerm

end Goose.Lower.Validation

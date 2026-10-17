import Goose.Lower.Validation.PermissionPreservationFresh
import Goose.Lower.Validation.JoinContentsPatch

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem WritableClosed.patchTerm {le : LEnv} {before after : LS}
    {result : Unit} {term : Term} {current : BlockId} {authorized contents : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : patchTerm current term le before = (result, after))
    (closed : WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized contents)
    (edges : ∀ edge ∈ term.permissionEdges, ∀ destination,
      (permissionFunc le before).blocks[edge.1]? = some destination →
      ∀ entry ∈ destination.params.zip edge.2, authorized entry.1.1 → authorized entry.2) :
    WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized contents := by
  have sameVals : after.vals = before.vals := by
    rw [patchTerm_run current term] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    rfl
  have afterDense := (dense_patchTerm current term le before result after run checked bounded).1
  constructor
  · intro value member
    rw [permissionFunc_numValues afterDense le, sameVals]
    simpa only [permissionFunc_numValues checked le] using closed.bounded value member
  · intro block row param member permitted
    obtain ⟨old, oldRow, params⟩ := join_patchTerm_frame_at run row
    rw [sameVals]
    exact closed.entry old oldRow param (by rw [← params]; exact member) permitted
  · intro block blockMember value op member permitted
    obtain ⟨old, oldMember, _, instructions⟩ := join_patchTerm_frame_blocks run blockMember
    have oldInstruction : Inst.def value op ∈ old.insts := by
      rcases instructions with same | same
      · rw [same] at member; exact member
      · rw [same, List.mem_append, List.mem_singleton] at member
        rcases member with member | impossible
        · exact member
        · cases impossible
    exact (closed.definitions old oldMember value op oldInstruction permitted).retained
      (types_patchTerm current term le before result after run)
  · intro block blockMember actual member edge edgeMember destination row entry entryMember permitted
    obtain ⟨old, oldMember, _, instructions⟩ := join_patchTerm_frame_blocks run blockMember
    obtain ⟨oldDestination, oldRow, params⟩ := join_patchTerm_frame_at run row
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


theorem FreshWritableEvidence.patchTerm_before {le : LEnv} {first : Nat} {before after : LS}
    {value current : Nat} {result : Unit} {term : Term}
    (evidence : FreshWritableEvidence le first before value)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : patchTerm current term le before = (result, after))
    (targets : ∀ edge ∈ term.permissionEdges, ∀ destination,
      (permissionFunc le before).blocks[edge.1]? = some destination →
      ∀ param ∈ destination.params, param.1 < first) :
    FreshWritableEvidence le first after value := by
  obtain ⟨writable, contents, bindings, elements, bindingParams, contentParams, permitted, freshW, freshC⟩ := evidence
  refine ⟨writable, contents, bindings.patchTerm checked bounded run ?_,
    elements.patchTerm checked bounded run ?_, bindingParams.patchTerm run,
    contentParams.patchTerm run, permitted, freshW, freshC⟩
  · intro edge member destination row entry belongs allowed
    have old := targets edge member destination row entry.1 (List.of_mem_zip belongs).1
    exact (Nat.not_lt_of_ge (freshW _ allowed) old).elim
  · intro edge member destination row entry belongs allowed
    have old := targets edge member destination row entry.1 (List.of_mem_zip belongs).1
    exact (Nat.not_lt_of_ge (freshC _ allowed) old).elim

theorem FreshWritableEvidence.emitTerm_before {le : LEnv} {first : Nat} {before after : LS}
    {value : ValueId} {result : Unit} {term : Term}
    (evidence : FreshWritableEvidence le first before value)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : emitTerm term le before = (result, after))
    (targets : ∀ edge ∈ term.permissionEdges, ∀ destination,
      (permissionFunc le before).blocks[edge.1]? = some destination →
      ∀ param ∈ destination.params, param.1 < first) :
    FreshWritableEvidence le first after value := by
  cases live : before.cur with
  | none =>
    rw [emitTerm_none term le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact evidence
  | some current =>
    obtain ⟨writable, contents, bindings, elements, bindingParams, contentParams, permitted, freshW, freshC⟩ := evidence
    refine ⟨writable, contents, bindings.emitTerm checked bounded live run ?_,
      elements.emitTerm checked bounded live run ?_, bindingParams.emitTerm live run,
      contentParams.emitTerm live run, permitted, freshW, freshC⟩
    · intro edge member destination row entry belongs allowed
      have old := targets edge member destination row entry.1 (List.of_mem_zip belongs).1
      exact (Nat.not_lt_of_ge (freshW _ allowed) old).elim
    · intro edge member destination row entry belongs allowed
      have old := targets edge member destination row entry.1 (List.of_mem_zip belongs).1
      exact (Nat.not_lt_of_ge (freshC _ allowed) old).elim

theorem FreshWritableEvidence.setCur {le : LEnv} {first : Nat} {before after : LS}
    {value : ValueId} {result : Unit} {current : Option BlockId}
    (evidence : FreshWritableEvidence le first before value)
    (run : setCur current le before = (result, after)) : FreshWritableEvidence le first after value := by
  rw [setCur_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact evidence

#print axioms WritableClosed.patchTerm
#print axioms FreshWritableEvidence.patchTerm_before
#print axioms FreshWritableEvidence.emitTerm_before

end Goose.Lower.Validation

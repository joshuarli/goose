import Goose.Lower.Validation.PermissionPreservationFreshRules
import Goose.Lower.Validation.PermissionPreservationJoinGraph

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem WritableClosed.patchBrs_avoiding_target {le : LEnv} {before after : LS} {result : Unit}
    {target : BlockId} (incoming : List (BlockId × ValueId)) {authorized contents : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : Goose.Lower.patchBrs target incoming le before = (result, after))
    (closed : WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized contents)
    (excluded : ∀ destination, (permissionFunc le before).blocks[target]? = some destination →
      ∀ parameter ∈ destination.params, ¬ authorized parameter.1) :
    WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized contents := by
  induction incoming generalizing before after result with
  | nil => obtain ⟨_,rfl⟩ := pure_eq.mp run; exact closed
  | cons pair rest ih =>
    obtain ⟨stepResult,middle,firstRun,restRun⟩ := bind_eq.mp run
    have middleFacts := dense_patchTerm pair.1 (.br target [pair.2]) le before stepResult middle firstRun checked bounded
    apply ih middleFacts.1 middleFacts.2.1 restRun
    · apply closed.patchTerm checked bounded firstRun
      intro edge member destination row entry belongs permitted
      have same : edge = (target,[pair.2]) := by simpa [Term.permissionEdges] using member
      subst edge
      exact (excluded destination row entry.1 (List.of_mem_zip belongs).1 permitted).elim
    · intro destination row parameter member permitted
      obtain ⟨old,oldRow,params⟩ := join_patchTerm_frame_at firstRun row
      exact excluded old oldRow parameter (by rw [← params]; exact member) permitted

theorem FreshWritableEvidence.patchBrs_before {le : LEnv} {before after : LS} {first : Nat}
    {target : BlockId} {value : ValueId} {result : Unit} (incoming : List (BlockId × ValueId))
    (evidence : FreshWritableEvidence le first before value)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : Goose.Lower.patchBrs target incoming le before = (result,after))
    (earlier : ∀ destination, (permissionFunc le before).blocks[target]? = some destination →
      ∀ parameter ∈ destination.params, parameter.1 < first) :
    FreshWritableEvidence le first after value := by
  obtain ⟨writable,contents,bindings,elements,bindingParams,contentParams,permitted,freshW,freshC⟩ := evidence
  refine ⟨writable,contents,bindings.patchBrs_avoiding_target incoming checked bounded run ?_,
    elements.patchBrs_avoiding_target incoming checked bounded run ?_,bindingParams.patchBrs incoming run,
    contentParams.patchBrs incoming run,permitted,freshW,freshC⟩
  · intro destination row parameter member allowed
    exact Nat.not_lt_of_ge (freshW _ allowed) (earlier destination row parameter member)
  · intro destination row parameter member allowed
    exact Nat.not_lt_of_ge (freshC _ allowed) (earlier destination row parameter member)

theorem FreshPermissionInstruction.patchBrs_before {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {instruction : Inst} {target : BlockId} {result : Unit}
    (incoming : List (BlockId × ValueId))
    (permitted : FreshPermissionInstruction module func le first before instruction)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : Goose.Lower.patchBrs target incoming le before = (result,after))
    (earlier : ∀ destination, (permissionFunc le before).blocks[target]? = some destination →
      ∀ parameter ∈ destination.params, parameter.1 < first) :
    FreshPermissionInstruction module func le first after instruction := by
  have types := types_patchBrs target incoming le before result after run
  constructor
  · apply (permitted.1.retained permitted.2 types).mono
    · intro value evidence
      exact evidence.patchBrs_before incoming checked bounded run earlier
    · intro value evidence
      exact evidence.patchBrs_before incoming checked bounded run earlier
  · exact permitted.2.retained types

theorem FreshContentsEvidence.newBlock {le : LEnv} {first : Nat} {before after : LS}
    {value : ValueId} {result : BlockId × List ValueId} {types : List VTy}
    (evidence : FreshContentsEvidence le first before value)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : Goose.Lower.newBlock types le before = (result,after)) : FreshContentsEvidence le first after value := by
  obtain ⟨contents,elements,parameters,permitted,fresh⟩ := evidence
  have oldBound : ∀ candidate, contents candidate → candidate < before.vals.size := by
    intro candidate member
    simpa only [permissionFunc_numValues checked le] using elements.bounded candidate member
  exact ⟨contents,elements.newBlock_preserve checked bounded run,
    parameters.newBlock_preserve run oldBound,permitted,fresh⟩

theorem FreshWritableEvidence.newBlock {le : LEnv} {first : Nat} {before after : LS}
    {value : ValueId} {result : BlockId × List ValueId} {types : List VTy}
    (evidence : FreshWritableEvidence le first before value)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : Goose.Lower.newBlock types le before = (result,after)) : FreshWritableEvidence le first after value := by
  obtain ⟨writable,contents,bindings,elements,bindingParams,contentParams,permitted,freshW,freshC⟩ := evidence
  have oldW : ∀ candidate, writable candidate → candidate < before.vals.size := by
    intro candidate member
    simpa only [permissionFunc_numValues checked le] using bindings.bounded candidate member
  have oldC : ∀ candidate, contents candidate → candidate < before.vals.size := by
    intro candidate member
    simpa only [permissionFunc_numValues checked le] using elements.bounded candidate member
  exact ⟨writable,contents,bindings.newBlock_preserve checked bounded run,
    elements.newBlock_preserve checked bounded run,bindingParams.newBlock_preserve run oldW,
    contentParams.newBlock_preserve run oldC,permitted,freshW,freshC⟩

theorem FreshPermissionInstruction.newBlock {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {instruction : Inst} {result : BlockId × List ValueId} {types : List VTy}
    (permitted : FreshPermissionInstruction module func le first before instruction)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : Goose.Lower.newBlock types le before = (result,after)) :
    FreshPermissionInstruction module func le first after instruction := by
  have extension := types_newBlock types le before result after run
  constructor
  · apply (permitted.1.retained permitted.2 extension).mono
    · intro value evidence
      exact evidence.newBlock checked bounded run
    · intro value evidence
      exact evidence.newBlock checked bounded run
  · exact permitted.2.retained extension

#print axioms WritableClosed.patchBrs_avoiding_target
#print axioms FreshPermissionInstruction.patchBrs_before
#print axioms FreshPermissionInstruction.newBlock

end Goose.Lower.Validation

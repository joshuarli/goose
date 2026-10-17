import Goose.Lower.Validation.PermissionInstructionControlGraph

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem newBlock_target_excluded {le : LEnv} {before allocated : LS}
    {result : BlockId × List ValueId} {types : List VTy} {authorized : ValueId → Prop}
    (run : Goose.Lower.newBlock types le before = (result,allocated))
    (oldBound : ∀ candidate, authorized candidate → candidate < before.vals.size) :
    ∀ destination, (permissionFunc le allocated).blocks[result.1]? = some destination →
      ∀ parameter ∈ destination.params, ¬ authorized parameter.1 := by
  rw [newBlock_run_general] at run
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
  intro destination row parameter member permitted
  have newRow :
      (permissionFunc le { before with
        blocks := before.blocks.push ⟨(paramIds types before.vals).zip types,#[]⟩
        vals := pushParamTypes types before.vals }).blocks[before.blocks.size]? =
      some ⟨(paramIds types before.vals).zip types,[]⟩ := by
    simp [permissionFunc]
    simpa only [Array.size_map] using (Array.getElem_push_eq
      (xs := before.blocks.map fun block => (⟨block.params,block.insts.toList⟩ : GIR.Block))
      (x := (⟨(paramIds types before.vals).zip types,[]⟩ : GIR.Block)))
  rw [newRow] at row
  cases Option.some.inj row
  exact Nat.not_lt_of_ge (paramIds_lower_bound member) (oldBound parameter.1 permitted)

theorem ContentsClosed.newBlock_patchBrs {le : LEnv} {before allocated after : LS}
    {result : BlockId × List ValueId} {patched : Unit} {types : List VTy}
    (incoming : List (BlockId × ValueId)) {authorized : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (allocation : Goose.Lower.newBlock types le before = (result,allocated))
    (run : Goose.Lower.patchBrs result.1 incoming le allocated = (patched,after))
    (closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized) :
    ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized := by
  have allocatedDense := dense_newBlock types le before result allocated allocation checked bounded
  apply (closed.newBlock_preserve checked bounded allocation).patchBrs_avoiding_target incoming
    allocatedDense.1 allocatedDense.2.1 run
  apply newBlock_target_excluded allocation
  intro candidate member
  simpa only [permissionFunc_numValues checked le] using closed.bounded candidate member

theorem WritableClosed.newBlock_patchBrs {le : LEnv} {before allocated after : LS}
    {result : BlockId × List ValueId} {patched : Unit} {types : List VTy}
    (incoming : List (BlockId × ValueId)) {authorized contents : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (allocation : Goose.Lower.newBlock types le before = (result,allocated))
    (run : Goose.Lower.patchBrs result.1 incoming le allocated = (patched,after))
    (closed : WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized contents) :
    WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized contents := by
  have allocatedDense := dense_newBlock types le before result allocated allocation checked bounded
  apply (closed.newBlock_preserve checked bounded allocation).patchBrs_avoiding_target incoming
    allocatedDense.1 allocatedDense.2.1 run
  apply newBlock_target_excluded allocation
  intro candidate member
  simpa only [permissionFunc_numValues checked le] using closed.bounded candidate member

theorem FreshContentsEvidence.newBlock_patchBrs {le : LEnv} {first : Nat} {before allocated after : LS}
    {value : ValueId} {result : BlockId × List ValueId} {patched : Unit} {types : List VTy}
    (incoming : List (BlockId × ValueId))
    (evidence : FreshContentsEvidence le first before value)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (allocation : Goose.Lower.newBlock types le before = (result,allocated))
    (run : Goose.Lower.patchBrs result.1 incoming le allocated = (patched,after)) :
    FreshContentsEvidence le first after value := by
  obtain ⟨contents,elements,parameters,permitted,fresh⟩ := evidence
  have oldBound : ∀ candidate, contents candidate → candidate < before.vals.size := by
    intro candidate member
    simpa only [permissionFunc_numValues checked le] using elements.bounded candidate member
  exact ⟨contents,elements.newBlock_patchBrs incoming checked bounded allocation run,
    (parameters.newBlock_preserve allocation oldBound).patchBrs incoming run,permitted,fresh⟩

theorem FreshWritableEvidence.newBlock_patchBrs {le : LEnv} {first : Nat} {before allocated after : LS}
    {value : ValueId} {result : BlockId × List ValueId} {patched : Unit} {types : List VTy}
    (incoming : List (BlockId × ValueId))
    (evidence : FreshWritableEvidence le first before value)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (allocation : Goose.Lower.newBlock types le before = (result,allocated))
    (run : Goose.Lower.patchBrs result.1 incoming le allocated = (patched,after)) :
    FreshWritableEvidence le first after value := by
  obtain ⟨writable,contents,bindings,elements,bindingParams,contentParams,permitted,freshW,freshC⟩ := evidence
  have oldW : ∀ candidate, writable candidate → candidate < before.vals.size := by
    intro candidate member
    simpa only [permissionFunc_numValues checked le] using bindings.bounded candidate member
  have oldC : ∀ candidate, contents candidate → candidate < before.vals.size := by
    intro candidate member
    simpa only [permissionFunc_numValues checked le] using elements.bounded candidate member
  exact ⟨writable,contents,bindings.newBlock_patchBrs incoming checked bounded allocation run,
    elements.newBlock_patchBrs incoming checked bounded allocation run,
    (bindingParams.newBlock_preserve allocation oldW).patchBrs incoming run,
    (contentParams.newBlock_preserve allocation oldC).patchBrs incoming run,permitted,freshW,freshC⟩

theorem FreshPermissionInstruction.newBlock_patchBrs {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before allocated after : LS} {instruction : Inst}
    {result : BlockId × List ValueId} {patched : Unit} {types : List VTy}
    (incoming : List (BlockId × ValueId))
    (permitted : FreshPermissionInstruction module func le first before instruction)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (allocation : Goose.Lower.newBlock types le before = (result,allocated))
    (run : Goose.Lower.patchBrs result.1 incoming le allocated = (patched,after)) :
    FreshPermissionInstruction module func le first after instruction := by
  have extension := (types_newBlock types le before result allocated allocation).trans
    (types_patchBrs result.1 incoming le allocated patched after run)
  constructor
  · apply (permitted.1.retained permitted.2 extension).mono
    · intro value evidence
      exact evidence.newBlock_patchBrs incoming checked bounded allocation run
    · intro value evidence
      exact evidence.newBlock_patchBrs incoming checked bounded allocation run
  · exact permitted.2.retained extension

theorem FreshContentsEvidence.joinValue {le : LEnv} {first : Nat} {before after : LS}
    {value result yesValue noValue : ValueId} {yes no : Option BlockId}
    (evidence : FreshContentsEvidence le first before value)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : Goose.Lower.joinValue yes yesValue no noValue le before = (result,after)) :
    FreshContentsEvidence le first after value := by
  unfold Goose.Lower.joinValue at run
  split at run
  · simp only [bind_eq,setCur_run] at run
    obtain ⟨ignored,entered,entry,finish⟩ := run
    obtain ⟨_,rfl⟩ := Prod.mk.inj entry
    rw [pure_run] at finish
    obtain ⟨_,rfl⟩ := Prod.mk.inj finish
    exact evidence
  · simp only [bind_eq] at run
    obtain ⟨ty,typed,typeRun,join,allocated,allocation,patched,middle,patchRun,
      ignored,entered,entry,finish⟩ := run
    have typedSame : typed = before := by
      have same := valTy_run
        (((yes.map fun b => (b,yesValue)).toList ++ (no.map fun b => (b,noValue)).toList).headD (0,0)).2 le before
      rw [typeRun] at same
      exact same
    subst typed
    have retained := evidence.newBlock_patchBrs _ checked bounded allocation patchRun
    rw [setCur_run] at entry
    obtain ⟨_,rfl⟩ := Prod.mk.inj entry
    rw [pure_run] at finish
    obtain ⟨_,rfl⟩ := Prod.mk.inj finish
    exact retained

theorem FreshWritableEvidence.joinValue {le : LEnv} {first : Nat} {before after : LS}
    {value result yesValue noValue : ValueId} {yes no : Option BlockId}
    (evidence : FreshWritableEvidence le first before value)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : Goose.Lower.joinValue yes yesValue no noValue le before = (result,after)) :
    FreshWritableEvidence le first after value := by
  unfold Goose.Lower.joinValue at run
  split at run
  · simp only [bind_eq,setCur_run] at run
    obtain ⟨ignored,entered,entry,finish⟩ := run
    obtain ⟨_,rfl⟩ := Prod.mk.inj entry
    rw [pure_run] at finish
    obtain ⟨_,rfl⟩ := Prod.mk.inj finish
    exact evidence
  · simp only [bind_eq] at run
    obtain ⟨ty,typed,typeRun,join,allocated,allocation,patched,middle,patchRun,
      ignored,entered,entry,finish⟩ := run
    have typedSame : typed = before := by
      have same := valTy_run
        (((yes.map fun b => (b,yesValue)).toList ++ (no.map fun b => (b,noValue)).toList).headD (0,0)).2 le before
      rw [typeRun] at same
      exact same
    subst typed
    have retained := evidence.newBlock_patchBrs _ checked bounded allocation patchRun
    rw [setCur_run] at entry
    obtain ⟨_,rfl⟩ := Prod.mk.inj entry
    rw [pure_run] at finish
    obtain ⟨_,rfl⟩ := Prod.mk.inj finish
    exact retained

theorem FreshPermissionInstruction.joinValue {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {instruction : Inst}
    {result yesValue noValue : ValueId} {yes no : Option BlockId}
    (permitted : FreshPermissionInstruction module func le first before instruction)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : Goose.Lower.joinValue yes yesValue no noValue le before = (result,after)) :
    FreshPermissionInstruction module func le first after instruction := by
  have extension := types_joinValue yes yesValue no noValue le before result after run
  constructor
  · apply (permitted.1.retained permitted.2 extension).mono
    · intro value evidence
      exact evidence.joinValue checked bounded run
    · intro value evidence
      exact evidence.joinValue checked bounded run
  · exact permitted.2.retained extension

#print axioms ContentsClosed.newBlock_patchBrs
#print axioms WritableClosed.newBlock_patchBrs
#print axioms FreshPermissionInstruction.newBlock_patchBrs
#print axioms FreshPermissionInstruction.joinValue

end Goose.Lower.Validation

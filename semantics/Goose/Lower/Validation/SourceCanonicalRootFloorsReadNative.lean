import Goose.Lower.Validation.SourceCanonicalRootFloorsFacts
import Goose.Lower.Validation.SourceCanonicalRootFloorsNativeTyping

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR ProvenanceConvergence ReplacementContentFlowSource

theorem SourceCanonicalTables.readVar_annotation_floor {env : PEnv} {func : Func}
    (tables : SourceCanonicalTables env func) {localEnv : LEnv} {before after : LS}
    {slot : VarId} {localVar : LocalVar} {value : ValueId}
    (sourceVar : env.impl.vars[slot]? = some localVar) (reference : localVar.ty.isRefLike = true)
    (ordinary : localVar.ty.isRefSlice = false) (generated : GeneratedBuilderState before)
    (run : lowerExpr (.read (.var slot)) localEnv before = (value, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after) :
    ((env.ann slot).getD []) ⊆
      rootsAt (func.provenance (resultRoots (lower env.mod) (lower env.mod).implTypes)
        (func.valueTypes (lower env.mod)) (lower env.mod).rootCount).vals value := by
  obtain ⟨slotRow, slotAt, slotType⟩ := tables.variables slot localVar sourceVar
  obtain ⟨address, addressBlock, loadBlock, addressMember, loadMember, addressDef, loadDef⟩ :=
    lowerExpr_readVar_native_definitions generated run live continuation
  have addressRoot := provenance_slotAddr (resultRoots (lower env.mod) (lower env.mod).implTypes)
    (func.valueTypes (lower env.mod)) func (lower env.mod).rootCount addressMember addressDef
    (tables.definitions _ addressMember _ _ addressDef)
  have valueType := lowerExpr_readVar_native_type generated run live continuation rfl tables.native slotAt
  have refLike : valRefLike (func.valueTypes (lower env.mod)) value = true := by
    simp only [valRefLike, valueType, VTy.refLike, slotType, reference]
  have closed := provenance_instructionRootsClosed (types := func.valueTypes (lower env.mod))
    tables.rootUniverse (lower env.mod).rootCount tables.rootCount
  have valueBound : value <
      (func.provenance (resultRoots (lower env.mod) (lower env.mod).implTypes)
        (func.valueTypes (lower env.mod)) (lower env.mod).rootCount).vals.size := by
    rw [(provenance_sizes _ _ _ _).2]
    exact tables.definitions _ loadMember _ _ loadDef
  intro root member
  apply provenance_closed_load_local closed loadMember loadDef valueBound refLike addressRoot
  exact canonical_slot_seed_floor _ _ _ _ slot root
    (tables.annotations slot localVar sourceVar reference ordinary member)

theorem SourceCanonicalTables.read_parameter_contents_floor {env : PEnv} {func : Func}
    (tables : SourceCanonicalTables env func) {localEnv : LEnv} {before after : LS}
    {slot : VarId} {localVar : LocalVar} {value : ValueId} {roots : List RootRef}
    (sourceVar : env.impl.vars[slot]? = some localVar) (reference : localVar.ty.isRefSlice = true)
    (contents : env.cont slot = some roots) (generated : GeneratedBuilderState before)
    (run : lowerExpr (.read (.deref (.read (.var slot)))) localEnv before = (value, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after) :
    roots ⊆ rootsAt (func.provenance (resultRoots (lower env.mod) (lower env.mod).implTypes)
      (func.valueTypes (lower env.mod)) (lower env.mod).rootCount).vals value := by
  obtain ⟨address, middle, emitted, innerRun, loadRun, middleGenerated, middleLive, emittedLive,
    middleContinuation, emittedContinuation⟩ := lowerExpr_read_native_checkpoints generated run live continuation
  change lowerExpr (.read (.var slot)) localEnv before = (address, middle) at innerRun
  obtain ⟨nativeSlot, slotAt, slotType⟩ := tables.variables slot localVar sourceVar
  obtain ⟨formal, formalAt, formalReference, ownSeed, rootsIncluded⟩ := tables.contents slot roots contents
  obtain ⟨slotAddress, addressBlock, innerLoadBlock, addressMember, innerLoadMember,
    addressDef, innerLoadDef⟩ :=
    lowerExpr_readVar_native_definitions generated innerRun middleLive middleContinuation
  have slotAddressRoot := provenance_slotAddr (resultRoots (lower env.mod) (lower env.mod).implTypes)
    (func.valueTypes (lower env.mod)) func (lower env.mod).rootCount addressMember addressDef
    (tables.definitions _ addressMember _ _ addressDef)
  have innerType := lowerExpr_readVar_native_type generated innerRun middleLive middleContinuation
    rfl tables.native slotAt
  rw [slotType] at innerType
  have shape : ∃ mode sliceMode element, localVar.ty = .ref mode (.slice sliceMode element) := by
    cases typeAt : localVar.ty <;> simp_all [Ty.isRefSlice]
    case ref mode target => cases target <;> simp_all
  obtain ⟨mode, sliceMode, element, typeAt⟩ := shape
  have innerRefLike : valRefLike (func.valueTypes (lower env.mod)) address = true := by
    simp only [valRefLike, innerType, VTy.refLike, typeAt, Ty.isRefLike]
  have closed := provenance_instructionRootsClosed (types := func.valueTypes (lower env.mod))
    tables.rootUniverse (lower env.mod).rootCount tables.rootCount
  have innerBound : address <
      (func.provenance (resultRoots (lower env.mod) (lower env.mod).implTypes)
        (func.valueTypes (lower env.mod)) (lower env.mod).rootCount).vals.size := by
    rw [(provenance_sizes _ _ _ _).2]
    exact tables.definitions _ innerLoadMember _ _ innerLoadDef
  have parameterRoot : RootRef.param slot ∈
      rootsAt (func.provenance (resultRoots (lower env.mod) (lower env.mod).implTypes)
        (func.valueTypes (lower env.mod)) (lower env.mod).rootCount).vals address := by
    apply provenance_closed_load_local closed innerLoadMember innerLoadDef innerBound innerRefLike slotAddressRoot
    exact canonical_slot_seed_floor _ _ _ _ slot (.param slot) ownSeed
  obtain ⟨loadBlock, loadMember, loadDef⟩ :=
    emitted_definition_native middleGenerated loadRun emittedLive emittedContinuation
  have loadedType := checked_load_type (tables.native _ loadMember _ _ loadDef) rfl
    (by simpa only [typeAt] using innerType)
  intro root member
  exact emitted_load_contents_canonical_floor middleGenerated loadRun emittedLive emittedContinuation
    (tables.definitions _ loadMember _ _ loadDef) tables.rootUniverse (lower env.mod).rootCount
    tables.rootCount loadedType formalAt formalReference parameterRoot (rootsIncluded member)

end Goose.Lower.Validation.SourceCanonicalRootFloors

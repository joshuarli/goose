import Goose.Lower.Validation.SourceCanonicalRootFloorsNativeDefinitions

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR ReplacementContentFlowSource

theorem checked_definition_type {func : Func} {env : TyEnv} {types : Array (Option VTy)}
    {value : ValueId} {op : Op} {type : VTy}
    (checked : checkInstTypes func env types (.def value op) = .ok ())
    (produced : op.resultTy env = .ok type) : types[value]? = some (some type) := by
  by_cases row : types[value]? = some (some type)
  · exact row
  · simp [checkInstTypes, produced, row, bind, Except.bind] at checked

theorem checked_slotAddr_type {func : Func} {env : TyEnv} {types : Array (Option VTy)}
    {value : ValueId} {slot : SlotId} {row : GIR.Slot}
    (checked : checkInstTypes func env types (.def value (.slotAddr slot)) = .ok ())
    (slotAt : env.slots[slot]? = some row) :
    ∃ mode, types[value]? = some (some (.data (.ref mode row.ty))) := by
  have produced : ∃ mode, Op.resultTy env (.slotAddr slot) = .ok (.data (.ref mode row.ty)) := by
    simp only [Op.resultTy, slotAt, pure, Except.pure]
    exact ⟨_, rfl⟩
  obtain ⟨mode, result⟩ := produced
  exact ⟨mode, checked_definition_type checked result⟩

theorem checked_load_type {func : Func} {env : TyEnv} {types : Array (Option VTy)}
    {value address : ValueId} {mode : Mutability} {type : Ty}
    (checked : checkInstTypes func env types (.def value (.load address)) = .ok ())
    (values : env.vals = types) (addressAt : types[address]? = some (some (.data (.ref mode type)))) :
    types[value]? = some (some (.data type)) := by
  apply checked_definition_type checked
  simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, values, addressAt,
    bind, Except.bind, pure, Except.pure]

theorem lowerExpr_readVar_native_definitions {env : LEnv} {before after : LS}
    {slot : VarId} {value : ValueId} {func : Func} (generated : GeneratedBuilderState before)
    (run : lowerExpr (.read (.var slot)) env before = (value, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after) :
    ∃ address addressBlock loadBlock,
      addressBlock ∈ func.blocks.toList ∧ loadBlock ∈ func.blocks.toList ∧
      Inst.def address (.slotAddr slot) ∈ addressBlock.insts ∧
      Inst.def value (.load address) ∈ loadBlock.insts := by
  simp only [lowerExpr] at run
  obtain ⟨address, middle, placeRun, run⟩ := bind_eq.mp run
  obtain ⟨loaded, emitted, loadRun, run⟩ := bind_eq.mp run
  obtain ⟨recordResult, recorded, recordRun, run⟩ := bind_eq.mp run
  obtain ⟨rfl, rfl⟩ := pure_eq.mp run
  have emittedLive := (dead_recordReadValueRootRecipe loaded (.var slot)).live_before recordRun live
  have middleLive := (dead_emitDef (.load address)).live_before loadRun emittedLive
  have emittedContinuation := continuation.of_advance
    (advB_recordReadValueRootRecipe loaded (.var slot) _ _ _ _ recordRun)
  have middleContinuation := emittedContinuation.of_advance (adv_emitDef loadRun)
  obtain ⟨addressBlock, addressMember, addressDef⟩ :=
    emitted_definition_native generated placeRun middleLive middleContinuation
  obtain ⟨loadBlock, loadMember, loadDef⟩ :=
    emitted_definition_native (generated.lowerPlace _ placeRun) loadRun emittedLive emittedContinuation
  exact ⟨address, addressBlock, loadBlock, addressMember, loadMember, addressDef, loadDef⟩

theorem lowerExpr_readVar_native_type {env : LEnv} {before after : LS}
    {slot : VarId} {value : ValueId} {func : Func} (generated : GeneratedBuilderState before)
    (run : lowerExpr (.read (.var slot)) env before = (value, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after)
    {nativeEnv : TyEnv} {types : Array (Option VTy)} (values : nativeEnv.vals = types)
    (checked : ∀ block ∈ func.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → checkInstTypes func nativeEnv types (.def value op) = .ok ())
    {row : GIR.Slot} (slotAt : nativeEnv.slots[slot]? = some row) :
    types[value]? = some (some (.data row.ty)) := by
  obtain ⟨address, addressBlock, loadBlock, addressMember, loadMember, addressDef, loadDef⟩ :=
    lowerExpr_readVar_native_definitions generated run live continuation
  obtain ⟨mode, addressAt⟩ := checked_slotAddr_type (checked _ addressMember _ _ addressDef) slotAt
  exact checked_load_type (checked _ loadMember _ _ loadDef) values addressAt

theorem lowerExpr_read_native_checkpoints {env : LEnv} {before after : LS}
    {place : Place} {value : ValueId} {func : Func} (generated : GeneratedBuilderState before)
    (run : lowerExpr (.read place) env before = (value, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after) :
    ∃ address middle emitted,
      lowerPlace place env before = (address, middle) ∧
      emitDef (.load address) env middle = (value, emitted) ∧
      GeneratedBuilderState middle ∧ middle.cur.isSome = true ∧ emitted.cur.isSome = true ∧
      NativeBuilderContinuation func middle ∧ NativeBuilderContinuation func emitted := by
  simp only [lowerExpr] at run
  obtain ⟨address, middle, placeRun, run⟩ := bind_eq.mp run
  obtain ⟨loaded, emitted, loadRun, run⟩ := bind_eq.mp run
  obtain ⟨recordResult, recorded, recordRun, run⟩ := bind_eq.mp run
  obtain ⟨rfl, rfl⟩ := pure_eq.mp run
  have emittedLive := (dead_recordReadValueRootRecipe loaded place).live_before recordRun live
  have middleLive := (dead_emitDef (.load address)).live_before loadRun emittedLive
  have emittedContinuation := continuation.of_advance
    (advB_recordReadValueRootRecipe loaded place _ _ _ _ recordRun)
  exact ⟨address, middle, emitted, placeRun, loadRun, generated.lowerPlace _ placeRun,
    middleLive, emittedLive, emittedContinuation.of_advance (adv_emitDef loadRun), emittedContinuation⟩

end Goose.Lower.Validation.SourceCanonicalRootFloors

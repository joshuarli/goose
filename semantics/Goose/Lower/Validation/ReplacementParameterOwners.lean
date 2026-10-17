import Goose.Lower.Validation.ReplacementStaticOwners

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lowerPlace_parameter_owner_root
    {env : LEnv} {before captured state : LS} {module : GIR.Module} {func : Func}
    {results : Array (List RootRef)} {types : Array (Option VTy)}
    {value slot input position : Nat} {parameterType : VTy} {index : BlockId}
    (run : lowerPlace (.deref (.read (.var slot))) env before = (value, captured))
    (current : before.cur = some index) (live : LiveBound before)
    (extension : captured.Ext state) (blocks : func.blocks = finishBlocks state.blocks)
    (dense : state.DenseDefinitions) (member : func ∈ module.funcs.toList)
    (bounded : ProvenanceConvergence.RootBounds results func module.globals.size)
    {entry initBlock : GIR.Block} (entryAt : func.blocks[0]? = some entry)
    (parameterAt : entry.params[position]? = some (input, parameterType))
    (inputReference : valRefLike types input = true) (outputReference : valRefLike types value = true)
    (initMember : initBlock ∈ func.blocks.toList) {origin : OriginId}
    (initialized : .eff (.slotInit slot input origin) ∈ initBlock.insts)
    (slotBound : slot < func.slots.size) :
    RootRef.param position ∈ rootsAt (func.provenance results types (ProvenanceConvergence.moduleRootCount module)).vals value := by
  change (emitDef (.slotAddr slot) >>= fun address => do
    let value ← emitDef (.load address)
    recordReadValueRootRecipe value (.var slot)
    pure value) env before = (value, captured) at run
  obtain ⟨address, afterAddress, addressRun, rest⟩ := bind_eq.mp run
  obtain ⟨loadedValue, afterLoad, loadRun, rest⟩ := bind_eq.mp rest
  obtain ⟨_, afterRecord, recordRun, pureRun⟩ := bind_eq.mp rest
  obtain ⟨rfl, rfl⟩ := pure_eq.mp pureRun
  let provenance := func.provenance results types (ProvenanceConvergence.moduleRootCount module)
  have sizes := ProvenanceConvergence.provenance_sizes results types func (ProvenanceConvergence.moduleRootCount module)
  have closed := ProvenanceConvergence.provenance_module_instructionRootsClosed (types := types) member bounded
  have afterRecordExt : afterLoad.Ext afterRecord :=
    (advB_recordReadValueRootRecipe loadedValue (.var slot) env afterLoad () afterRecord recordRun).ext
  have afterLoadExt : afterLoad.Ext state := afterRecordExt.trans extension
  have afterAddressExt : afterAddress.Ext state := (adv_emitDef loadRun).ext.trans afterLoadExt
  have addressRoot : RootRef.local slot ∈ rootsAt provenance.vals address :=
    lowerPlace_static_provenance_root (.slot slot) addressRun current live afterAddressExt blocks dense member bounded
  have middleCurrent := (staticOwner_emitDef_current addressRun).trans current
  have middleLive := liveBound_of_adv (adv_emitDef addressRun) live
  obtain ⟨loadBlock, loadMember, loadDefinition⟩ := emitted_definition_retained middleCurrent
    (middleLive index middleCurrent) loadRun afterLoadExt blocks
  have outputBound : loadedValue < provenance.vals.size := by
    have defined : loadedValue ∈ func.blocks.toList.flatMap GIR.Block.defs := by
      apply List.mem_flatMap.mpr
      refine ⟨loadBlock, loadMember, List.mem_append_right _ ?_⟩
      exact List.mem_filterMap.mpr ⟨.def loadedValue (.load address), loadDefinition, rfl⟩
    have bound := List.mem_range.mp ((dense_finishBlocks dense blocks).mem_iff.mp defined)
    change loadedValue < (func.provenance results types (ProvenanceConvergence.moduleRootCount module)).vals.size
    simpa only [sizes.2] using bound
  have inputRoot : RootRef.param position ∈ rootsAt provenance.vals input :=
    provenance_ref_parameter_of_dense results types func _ (dense_finishBlocks dense blocks)
      entryAt parameterAt inputReference
  apply provenance_closed_load_local closed loadMember loadDefinition outputBound outputReference addressRoot
  exact closed.slotInit initMember initialized (by simpa only [sizes.1] using slotBound) inputRoot

end Goose.Lower.Validation

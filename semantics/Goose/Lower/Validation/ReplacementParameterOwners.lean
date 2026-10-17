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
  change (emitDef (.slotAddr slot) >>= fun address => emitDef (.load address)) env before = (value, captured) at run
  obtain ⟨address, middle, addressRun, loadRun⟩ := bind_eq.mp run
  let provenance := func.provenance results types (ProvenanceConvergence.moduleRootCount module)
  have sizes := ProvenanceConvergence.provenance_sizes results types func (ProvenanceConvergence.moduleRootCount module)
  have closed := ProvenanceConvergence.provenance_module_instructionRootsClosed (types := types) member bounded
  have addressRoot : RootRef.local slot ∈ rootsAt provenance.vals address :=
    lowerPlace_static_provenance_root (.slot slot) addressRun current live
      ((adv_emitDef loadRun).ext.trans extension) blocks dense member bounded
  have middleCurrent := (emitDef_current addressRun).trans current
  have middleLive := liveBound_of_adv (adv_emitDef addressRun) live
  obtain ⟨loadBlock, loadMember, loaded⟩ := emitted_definition_retained middleCurrent
    (middleLive index middleCurrent) loadRun extension blocks
  have outputBound : value < provenance.vals.size := by
    have defined : value ∈ func.blocks.toList.flatMap GIR.Block.defs := by
      apply List.mem_flatMap.mpr
      refine ⟨loadBlock, loadMember, List.mem_append_right _ ?_⟩
      exact List.mem_filterMap.mpr ⟨.def value (.load address), loaded, rfl⟩
    have bound := List.mem_range.mp ((dense_finishBlocks dense blocks).mem_iff.mp defined)
    change value < (func.provenance results types (ProvenanceConvergence.moduleRootCount module)).vals.size
    simpa only [sizes.2] using bound
  have inputRoot : RootRef.param position ∈ rootsAt provenance.vals input :=
    provenance_ref_parameter_of_dense results types func _ (dense_finishBlocks dense blocks)
      entryAt parameterAt inputReference
  apply provenance_closed_load_local closed loadMember loaded outputBound outputReference addressRoot
  exact closed.slotInit initMember initialized (by simpa only [sizes.1] using slotBound) inputRoot

end Goose.Lower.Validation

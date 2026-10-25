import Goose.GIR.AdmittedRegions
import Goose.Lower.Validation.SummaryPreservationSourceGlobalFunction
import Goose.Lower.Validation.SummaryPreservationAcceptedSummaries
import Goose.Lower.Validation.SummaryPreservationSourceReturnArity

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem accepted_global_return_value_roots_empty {module : Core.Module} {global : Core.Global}
    {index : GlobalId} {block : GIR.Block} {value : ValueId} {origin : Option OriginId}
    (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global)
    (blockMember : block ∈ (lowerGlobal module global).init.blocks.toList)
    (returnMember : Inst.term (.ret [value] origin) ∈ block.insts) :
    rootsAt ((lowerGlobal module global).init.provenance
      (resultRoots (lower module) (lower module).implTypes)
      ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount).vals value = [] := by
  obtain ⟨roots, after, upper, replayed, ready, returned⟩ :=
    accepted_global_replay_produced accepted globalRow (accepted_resultRoots_implTypes_below accepted)
  have actual := ready.finished_provenance (cfg_global_blocks module global)
    (global_provenance_seed module global _ upper ready.recipes) (lower module).rootCount
  have instruction : Inst.term (.ret [value] origin) ∈ (cfg_globalState module global).insts :=
    finishBlocks_instruction_member (by simpa only [cfg_global_blocks] using blockMember) returnMember
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro root member
  have impossible := returned value origin instruction root (actual.vals value root member)
  cases impossible

theorem accepted_global_admitted_return {module : Core.Module} {global : Core.Global}
    {index : GlobalId} {block : GIR.Block} {values : List ValueId} {origin : Option OriginId}
    (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global)
    (blockMember : block ∈ (lowerGlobal module global).init.blocks.toList)
    (returnMember : Inst.term (.ret values origin) ∈ block.insts) :
    (lowerGlobal module global).init.admittedInstruction (lower module)
      ((lowerGlobal module global).init.valueTypes (lower module))
      ((lowerGlobal module global).init.provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount)
      (.term (.ret values origin)) = true := by
  have instruction : Inst.term (.ret values origin) ∈ (cfg_globalState module global).insts :=
    finishBlocks_instruction_member (by simpa only [cfg_global_blocks] using blockMember) returnMember
  have arity := SourceReturnArity.global_return_arity module global values origin instruction
  cases values with
  | nil => rfl
  | cons value rest =>
    cases rest with
    | nil => simp [Func.admittedInstruction, accepted_global_return_value_roots_empty accepted globalRow blockMember returnMember]
    | cons second rest => simp at arity

#print axioms accepted_global_return_value_roots_empty
#print axioms accepted_global_admitted_return

end Goose.Lower.Validation.SummaryPreservation

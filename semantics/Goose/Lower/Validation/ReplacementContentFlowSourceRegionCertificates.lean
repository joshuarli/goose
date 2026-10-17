import Goose.GIR.AdmittedRegionsSound
import Goose.GIR.ReplacementContentFlowProofsSteps

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem admitted_return_step_within {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {state : State}
    {callees : Array State} {block : GIR.Block} {value : ValueId} {origin : Option OriginId}
    (checked : func.checkAdmittedRegions module types provenance = .ok ())
    (blockMember : block ∈ func.blocks.toList)
    (instruction : Inst.term (.ret [value] origin) ∈ block.insts)
    (reference : valRefLike types value = true)
    (returned : state.returned.NormalizedWithin func
      ((func.roots.results[0]?.getD []).flatMap func.expandParameterRoot))
    (operand : (flowAt state.values value).NormalizedWithin func
      ((rootsAt provenance.vals value).flatMap func.expandParameterRoot)) :
    (step module callees func types state (.term (.ret [value] origin))).returned.NormalizedWithin func
      ((func.roots.results[0]?.getD []).flatMap func.expandParameterRoot) := by
  rw [step_returned]
  apply returned.join
  apply operand.mono
  intro root member
  obtain ⟨source, sourceMember, expanded⟩ := List.mem_flatMap.mp member
  have permitted := func.checkAdmittedRegions_return checked blockMember instruction
    (value := value) (index := 0) (by simp) reference source sourceMember
  exact List.mem_flatMap.mpr ⟨source, permitted, expanded⟩

theorem admitted_parameter_store_within {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {state : State}
    {block : GIR.Block} {address value : ValueId} {origin : Option OriginId} {parameter : Nat}
    (checked : func.checkAdmittedRegions module types provenance = .ok ())
    (blockMember : block ∈ func.blocks.toList)
    (instruction : Inst.eff (.store address value origin) ∈ block.insts)
    (reference : valRefLike types value = true)
    (target : RootRef.param parameter ∈ rootsAt provenance.vals address)
    (sliceReference : (func.params[parameter]?).any Ty.isRefSlice = true)
    (operand : (flowAt state.values value).NormalizedWithin func
      ((rootsAt provenance.vals value).flatMap func.expandParameterRoot)) :
    ∃ ceiling, func.roots.contents.find? (·.1 == parameter) = some (parameter, ceiling) ∧
      (flowAt state.values value).NormalizedWithin func (ceiling.flatMap func.expandParameterRoot) := by
  obtain ⟨ceiling, row, within⟩ := func.checkAdmittedRegions_store checked blockMember instruction
    reference target sliceReference
  exact ⟨ceiling, row, operand.mono within⟩

theorem checkReturned_of_normalized_bound {func : Func} {state : State}
    {type : Ty} {declared : List RootRef}
    (result : func.results = [type]) (reference : type.isRefLike = true)
    (row : func.roots.results[0]? = some declared)
    (bounded : state.returned.NormalizedWithin func (declared.flatMap func.expandParameterRoot))
    (ready : state.returned ≠ .pending) : checkReturned func state = true := by
  obtain ⟨actual, known, within⟩ := bounded.actual ready
  simp only [checkReturned, result, reference, ite_true, row, Option.any_some, rootsWithin, known]
  exact List.all_eq_true.mpr fun root member => List.contains_iff_mem.mpr (within member)

#print axioms admitted_return_step_within
#print axioms admitted_parameter_store_within
#print axioms checkReturned_of_normalized_bound

end Goose.Lower.Validation.ReplacementContentFlowSource

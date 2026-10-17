import Goose.GIR.AdmittedRegionsSound
import Goose.Lower.Validation.AdmittedSourceCallsCoverage

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem Func.checkAdmittedRegions_argumentContents_subset {module : GIR.Module}
    {func callee : Func} {types : Array (Option VTy)} {provenance : Prov}
    (checked : func.checkAdmittedRegions module types provenance = .ok ())
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    {block : GIR.Block} (member : block ∈ func.blocks.toList)
    {value function : Nat} {arguments : List ValueId} {origin : Option OriginId}
    (called : Inst.def value (.call function arguments origin) ∈ block.insts)
    (calleeAt : module.funcs[function]? = some callee)
    {parameter : Nat} {ceiling : List RootRef}
    (row : (parameter, ceiling) ∈ callee.roots.contents.toList)
    (reference : (callee.params[parameter]?).any Ty.isRefSlice = true) :
    argumentContents func provenance arguments[parameter]! ⊆
      mapContentRoots func provenance arguments ceiling := by
  intro root rootMember
  obtain ⟨receiver, receiverMember, content, contentMember, expanded⟩ :=
    AdmittedSourceCalls.argumentContents_mem.mp rootMember
  have bounds := func.checkAdmittedRegions_call_receiver_reverse checked member called calleeAt row
    reference receiverMember
  exact AdmittedSourceCalls.mapContentRoots_mem.mpr
    (bounds.expanded closed content contentMember root expanded)

#print axioms Func.checkAdmittedRegions_argumentContents_subset

end Goose.Lower.Validation

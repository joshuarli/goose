import Goose.Lower.Validation.SourceOccurrenceInstructions
import Goose.Lower.Validation.AdmittedSourceOccurrenceReads

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR ReplacementContentFlowSource

theorem lowerContext_canonical_loadObserved_of_accepted {module : Core.Module}
    {context : Context} {impl : Impl} {index : ContextId}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl) :
    ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ value address,
      Inst.def value (.load address) ∈ block.insts →
      valRefLike ((lowerContextAt module context impl).valueTypes (lower module)) value = true →
      ∀ parameter, RootRef.param parameter ∈ rootsAt
        ((lowerContextAt module context impl).provenance
          (resultRoots (lower module) (lower module).implTypes)
          ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount).vals address →
        ((lowerContextAt module context impl).params[parameter]?).any Ty.isRefSlice = true →
        ((lowerContextAt module context impl).roots.contents.find? (·.1 == parameter)).isSome = true := by
  obtain ⟨upper, below, instructions⟩ :=
    accepted_context_instruction_occurrences accepted contextAt implAt
  intro block blockMember value address load reference parameter member _
  exact InstructionOccurrences.load_observed accepted implAt rfl
    (instructions block blockMember _ load) rfl reference (below.vals address) member

theorem lowerGlobal_canonical_loadObserved (module : Core.Module) (global : Core.Global) :
    ∀ parameter,
      ((lowerGlobal module global).init.params[parameter]?).any Ty.isRefSlice = true →
      ((lowerGlobal module global).init.roots.contents.find? (·.1 == parameter)).isSome = true := by
  intro parameter reference
  simp [lowerGlobal] at reference

#print axioms lowerContext_canonical_loadObserved_of_accepted
#print axioms lowerGlobal_canonical_loadObserved

end Goose.Lower.Validation

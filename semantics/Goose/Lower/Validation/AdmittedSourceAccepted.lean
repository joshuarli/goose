import Goose.Lower.Validation.SourceOccurrenceInstructions
import Goose.Lower.Validation.AdmittedSourceOccurrenceCallsAccepted
import Goose.Lower.Validation.AdmittedSourceOccurrenceStores
import Goose.Lower.Validation.SummaryPreservationAcceptedAdmission
import Goose.Lower.Validation.SummaryPreservationAcceptedReturnAdmission
import Goose.Lower.Validation.SummaryPreservationGlobalReturnAdmission

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR ReplacementContentFlowSource SummaryPreservation

theorem accepted_context_checkAdmittedRegions {module : Core.Module} {context : Context} {impl : Impl}
    {contextId : ContextId} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextId]? = some context)
    (implAt : module.impls[context.impl]? = some impl) :
    (lowerContextAt module context impl).checkAdmittedRegions (lower module)
      ((lowerContextAt module context impl).valueTypes (lower module))
      ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount) = .ok () := by
  have slots := accepted_function_admittedSlots accepted contextAt implAt
  have values := accepted_context_admittedValues accepted contextAt implAt
  rw [← module_implTypes_eq_native] at values
  obtain ⟨upper, below, occurrences⟩ := accepted_context_instruction_occurrences accepted contextAt implAt
  have instructions : ((lowerContextAt module context impl).blocks.toList.flatMap (·.insts)).all
      ((lowerContextAt module context impl).admittedInstruction (lower module)
        ((lowerContextAt module context impl).valueTypes (lower module))
        ((lowerContextAt module context impl).provenance
          (resultRoots (lower module) (lower module).implTypes)
          ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount)) = true := by
    apply List.all_eq_true.mpr
    intro instruction member
    obtain ⟨block, blockMember, present⟩ := List.mem_flatMap.mp member
    have occurrence := occurrences block blockMember instruction present
    cases instruction with
    | «def» value op =>
        cases op <;> try rfl
        rename_i callee arguments origin
        exact (occurrence.2.2.1 value callee arguments origin rfl).admitted_context
          accepted contextAt implAt rfl below _
    | eff effect =>
        cases effect <;> try rfl
        rename_i address value origin
        by_cases reference : valRefLike ((lowerContextAt module context impl).valueTypes (lower module)) value = true
        · have stored := occurrence.2.2.2.1 address value origin rfl reference
          exact stored.admitted_context accepted implAt rfl
            (fun argument {root} member => below.vals argument root member) _
        · simp [Func.admittedInstruction, reference]
    | term term =>
        cases term <;> try rfl
        exact accepted_function_admitted_return accepted contextAt implAt blockMember present
  simp [Func.checkAdmittedRegions, slots, values, instructions, pure, Except.pure]

theorem accepted_global_checkAdmittedRegions {module : Core.Module} {global : Core.Global}
    {index : GlobalId} (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[index]? = some global) :
    (lowerGlobal module global).init.checkAdmittedRegions (lower module)
      ((lowerGlobal module global).init.valueTypes (lower module))
      ((lowerGlobal module global).init.provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount) = .ok () := by
  have slots := lowerGlobal_admittedSlots module global
    ((lowerGlobal module global).init.provenance
      (resultRoots (lower module) (lower module).implTypes)
      ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount)
  have values := accepted_global_admittedValues accepted globalAt
  rw [← module_implTypes_eq_native] at values
  obtain ⟨upper, below, occurrences⟩ := accepted_global_instruction_occurrences accepted globalAt
  have instructions : ((lowerGlobal module global).init.blocks.toList.flatMap (·.insts)).all
      ((lowerGlobal module global).init.admittedInstruction (lower module)
        ((lowerGlobal module global).init.valueTypes (lower module))
        ((lowerGlobal module global).init.provenance
          (resultRoots (lower module) (lower module).implTypes)
          ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount)) = true := by
    apply List.all_eq_true.mpr
    intro instruction member
    obtain ⟨block, blockMember, present⟩ := List.mem_flatMap.mp member
    have occurrence := occurrences block blockMember instruction present
    cases instruction with
    | «def» value op =>
        cases op <;> try rfl
        rename_i callee arguments origin
        exact (occurrence.2.2.1 value callee arguments origin rfl).admitted_global accepted rfl _
    | eff effect =>
        cases effect <;> try rfl
        rename_i address value origin
        by_cases reference : valRefLike ((lowerGlobal module global).init.valueTypes (lower module)) value = true
        · have stored := occurrence.2.2.2.1 address value origin rfl reference
          exact stored.admitted_global rfl (fun argument {root} member => below.vals argument root member) _
        · simp [Func.admittedInstruction, reference]
    | term term =>
        cases term <;> try rfl
        exact accepted_global_admitted_return accepted globalAt blockMember present
  simp [Func.checkAdmittedRegions, slots, values, instructions, pure, Except.pure]

#print axioms accepted_context_checkAdmittedRegions
#print axioms accepted_global_checkAdmittedRegions

end Goose.Lower.Validation

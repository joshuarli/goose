import Goose.GIR.ReplacementContentFlowProofsScalarValues
import Goose.Lower.Validation.SourceOperandQueryBounds

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR ReplacementContentFlow.Model ReplacementContentFlowSource

theorem function_model_shape {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {final : State}
    (finalAt : ((replacementContentFlow module).forFunction func types).model = some final) :
    final.Shape func := by
  have closure := finalAt
  rw [ReplacementContentFlow.forFunction_model] at closure
  split at closure
  · cases statesAt : (replacementContentFlow module).model with
    | none => simp [statesAt] at closure
    | some states =>
      simp only [statesAt, Option.bind_some] at closure
      exact (closeFunctionFrom_reachable closure).extends.shape (start_shape func (func.valueTypes module))
  · simp at closure

theorem function_model_scalar_values {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {final : State}
    (typing : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      InstructionTyping module func (func.valueTypes module) inst)
    (finalAt : ((replacementContentFlow module).forFunction func types).model = some final) :
    ScalarCells (func.valueTypes module) final.values := by
  have closure := finalAt
  rw [ReplacementContentFlow.forFunction_model] at closure
  split at closure
  · cases statesAt : (replacementContentFlow module).model with
    | none => simp [statesAt] at closure
    | some states =>
      simp only [statesAt, Option.bind_some] at closure
      exact (closeFunctionFrom_reachable closure).scalar_values typing
  · simp at closure

theorem forFunction_scalar_dependencies_empty {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {value : ValueId} {roots : List RootRef}
    (typing : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      InstructionTyping module func (func.valueTypes module) inst)
    (bounded : value < func.numValues)
    (scalar : valRefLike (func.valueTypes module) value = false)
    (known : ((replacementContentFlow module).forFunction func types).ownerDependencies value = some roots) :
    roots = [] := by
  rw [ReplacementFunctionFlow.ownerDependencies_model] at known
  cases finalAt : ((replacementContentFlow module).forFunction func types).model with
  | none => simp [finalAt] at known
  | some final =>
    simp only [finalAt, Option.bind_some] at known
    have closure := finalAt
    rw [ReplacementContentFlow.forFunction_model] at closure
    split at closure
    · cases statesAt : (replacementContentFlow module).model with
      | none => simp [statesAt] at closure
      | some states =>
        simp only [statesAt, Option.bind_some] at closure
        have reachable := closeFunctionFrom_reachable closure
        have shape := reachable.extends.shape (start_shape func (func.valueTypes module))
        have emptyAtoms := reachable.scalar_values typing value (shape.values ▸ bounded) scalar
        cases rawAt : flowAt final.values value with
        | pending => simp [rawAt, ownerDependencies, rawOwnerTouches, Roots.bind, normalize] at known
        | unknown => simp [rawAt, Roots.AtomsWithin] at emptyAtoms
        | known atoms =>
          rw [rawAt] at emptyAtoms
          have nil : atoms = [] := List.eq_nil_iff_forall_not_mem.mpr (by
            intro atom member
            exact emptyAtoms atom member)
          simpa [rawAt, nil, ownerDependencies, rawOwnerTouches, Roots.bind, normalize] using known.symm
    · simp at closure

theorem lowerContext_scalar_operand_dependencies_empty_of_accepted {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {block : GIR.Block} (member : block ∈ (lowerContextAt module context impl).blocks.toList)
    {instruction : Inst} (instructionMember : instruction ∈ block.insts) {value : ValueId}
    (used : value ∈ instruction.uses)
    (scalar : valRefLike ((lowerContextAt module context impl).valueTypes (lower module)) value = false) :
    (replacementQueries (lower module) (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))).ownerDependencies value = some [] := by
  obtain ⟨roots, valueAt⟩ := accepted_context_factory_operand_value accepted contextAt implAt
    member instructionMember used
  obtain ⟨actual, actualAt, _⟩ := ReplacementFunctionFlow.ownerDependencies_of_value valueAt
  have bounded := (lowerContextAt_operand_bounds module context impl).1 block member instruction instructionMember value used
  have empty := forFunction_scalar_dependencies_empty
    (lowerContext_canonical_facts_of_accepted accepted contextAt implAt).typing bounded scalar actualAt
  rw [replacementQueries_ownerDependencies _ _ _ _ bounded, actualAt, empty]

theorem lowerGlobal_scalar_operand_dependencies_empty_of_accepted {module : Core.Module}
    {globalIndex : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ()) (globalAt : module.globals[globalIndex]? = some global)
    {block : GIR.Block} (member : block ∈ (lowerGlobal module global).init.blocks.toList)
    {instruction : Inst} (instructionMember : instruction ∈ block.insts) {value : ValueId}
    (used : value ∈ instruction.uses)
    (scalar : valRefLike ((lowerGlobal module global).init.valueTypes (lower module)) value = false) :
    (replacementQueries (lower module) (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))).ownerDependencies value = some [] := by
  obtain ⟨roots, valueAt⟩ := accepted_global_factory_operand_value accepted globalAt
    member instructionMember used
  obtain ⟨actual, actualAt, _⟩ := ReplacementFunctionFlow.ownerDependencies_of_value valueAt
  have bounded := (lowerGlobal_operand_bounds module global).1 block member instruction instructionMember value used
  have empty := forFunction_scalar_dependencies_empty
    (lowerGlobal_canonical_facts_of_accepted accepted globalAt).typing bounded scalar actualAt
  rw [replacementQueries_ownerDependencies _ _ _ _ bounded, actualAt, empty]

#print axioms function_model_shape
#print axioms function_model_scalar_values
#print axioms forFunction_scalar_dependencies_empty
#print axioms lowerContext_scalar_operand_dependencies_empty_of_accepted
#print axioms lowerGlobal_scalar_operand_dependencies_empty_of_accepted

end Goose.Lower.Validation

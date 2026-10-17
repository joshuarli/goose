import Goose.Lower.Validation.ProvenanceSourceBounds
import Goose.Lower.Validation.SourceSymbolSourceCheck
import Goose.Lower.Validation.ValidationTypedModuleEntry

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR ProvenanceConvergence

theorem lowerContextAt_provenance_base_bounds {module : Core.Module}
    {index : ContextId} {context : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl) :
    RootBounds #[] (lowerContextAt module context impl) (lower module).globals.size := by
  apply SymbolTableFacts.provenance_bounds (lowerContextAt_symbol_tables accepted contextAt implAt)
    (instructions := SourceSymbolSource.lowerContextAt_instruction_symbols accepted implAt)
  · intro block row
    obtain ⟨entry, entryAt, types⟩ := lowerContext_entry_types module context impl
    have same := Option.some.inj (entryAt.symm.trans row)
    subst entry
    have arity := congrArg List.length types
    simpa only [List.length_map] using Nat.le_of_eq arity
  all_goals simp [lowerEnv, lower, lowerContextAt, lowerImpl]

theorem lowerGlobal_provenance_base_bounds {module : Core.Module}
    {index : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ()) (globalAt : module.globals[index]? = some global) :
    RootBounds #[] (lowerGlobal module global).init (lower module).globals.size := by
  apply SymbolTableFacts.provenance_bounds (lowerGlobal_symbol_tables accepted globalAt)
    (instructions := SourceSymbolSource.lowerGlobal_instruction_symbols accepted globalAt)
  · intro block row
    obtain ⟨entry, entryAt, types⟩ := lowerGlobal_entry_types module global
    have same := Option.some.inj (entryAt.symm.trans row)
    subst entry
    have arity := congrArg List.length types
    simpa only [List.length_map] using Nat.le_of_eq arity
  all_goals simp [lowerEnv, lower, lowerGlobal]

theorem accepted_function_provenance_tables {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : FnId} {func : Func}
    (functionAt : (lower module).funcs[index]? = some func) :
    SymbolTableFacts (lower module) func ∧ RootBounds #[] func (lower module).globals.size := by
  cases contextAt : module.contexts[index]? with
  | none => simp [lower, Array.getElem?_map, contextAt] at functionAt
  | some context =>
    obtain ⟨impl, implAt, _⟩ := (Core.Sound.validate_modOk module accepted).ctx index context contextAt
    have same := Option.some.inj (functionAt.symm.trans (lower_func_at contextAt implAt))
    subst func
    exact ⟨lowerContextAt_symbol_tables accepted contextAt implAt,
      lowerContextAt_provenance_base_bounds accepted contextAt implAt⟩

theorem accepted_function_provenance_fixed {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : FnId} {func : Func}
    (functionAt : (lower module).funcs[index]? = some func) :
    provRound (resultRoots (lower module) (lower module).implTypes) (func.valueTypes (lower module)) func
        (func.provenance (resultRoots (lower module) (lower module).implTypes)
          (func.valueTypes (lower module)) (lower module).rootCount) =
      (func.provenance (resultRoots (lower module) (lower module).implTypes)
        (func.valueTypes (lower module)) (lower module).rootCount, false) := by
  have facts : ∀ f ∈ (lower module).funcs.toList,
      SymbolTableFacts (lower module) f ∧ RootBounds #[] f (lower module).globals.size := by
    intro f member
    obtain ⟨position, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    exact accepted_function_provenance_tables accepted row
  exact module_provenance_fixed_of_symbols (fun f member => (facts f member).1)
    (fun f member => (facts f member).2) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? functionAt))

theorem lowerContextAt_provenance_fixed {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : ContextId} {context : Context} {impl : Impl}
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl) :
    let func := lowerContextAt module context impl
    provRound (resultRoots (lower module) (lower module).implTypes) (func.valueTypes (lower module)) func
        (func.provenance (resultRoots (lower module) (lower module).implTypes)
          (func.valueTypes (lower module)) (lower module).rootCount) =
      (func.provenance (resultRoots (lower module) (lower module).implTypes)
        (func.valueTypes (lower module)) (lower module).rootCount, false) :=
  accepted_function_provenance_fixed accepted (lower_func_at contextAt implAt)

theorem accepted_resultRoots_global_bounds {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    ∀ index global, RootRef.global global ∈ rootsAt (resultRoots (lower module) (lower module).implTypes) index →
      global < (lower module).globals.size := by
  have facts : ∀ f ∈ (lower module).funcs.toList,
      SymbolTableFacts (lower module) f ∧ RootBounds #[] f (lower module).globals.size := by
    intro f member
    obtain ⟨position, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    exact accepted_function_provenance_tables accepted row
  exact resultRoots_global_bounds (fun f member => (facts f member).2)
    (declaredResultRoots_global_bounds (fun f member => (facts f member).1))

theorem lowerGlobal_provenance_fixed {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : GlobalId} {global : Core.Global}
    (globalAt : module.globals[index]? = some global) :
    let func := (lowerGlobal module global).init
    provRound (resultRoots (lower module) (lower module).implTypes) (func.valueTypes (lower module)) func
        (func.provenance (resultRoots (lower module) (lower module).implTypes)
          (func.valueTypes (lower module)) (lower module).rootCount) =
      (func.provenance (resultRoots (lower module) (lower module).implTypes)
        (func.valueTypes (lower module)) (lower module).rootCount, false) := by
  dsimp only
  have bounds := (lowerGlobal_provenance_base_bounds accepted globalAt).with_results
    (accepted_resultRoots_global_bounds accepted)
  apply provenance_fixed bounds.finite
  rw [finiteRootUniverse_length]
  simp only [lowerGlobal, List.length_nil, Array.size_empty, Nat.add_zero]
  unfold Module.rootCount
  omega

theorem accepted_function_instructionRootsClosed {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : FnId} {func : Func}
    (functionAt : (lower module).funcs[index]? = some func) :
    InstructionRootsClosed (resultRoots (lower module) (lower module).implTypes)
      (func.valueTypes (lower module)) func
      (func.provenance (resultRoots (lower module) (lower module).implTypes)
        (func.valueTypes (lower module)) (lower module).rootCount) := by
  apply instructionRootsClosed_of_quiet
  rw [accepted_function_provenance_fixed accepted functionAt]

theorem lowerContextAt_instructionRootsClosed {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : ContextId} {context : Context} {impl : Impl}
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl) :
    let func := lowerContextAt module context impl
    InstructionRootsClosed (resultRoots (lower module) (lower module).implTypes)
      (func.valueTypes (lower module)) func
      (func.provenance (resultRoots (lower module) (lower module).implTypes)
        (func.valueTypes (lower module)) (lower module).rootCount) :=
  accepted_function_instructionRootsClosed accepted (lower_func_at contextAt implAt)

theorem lowerGlobal_instructionRootsClosed {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : GlobalId} {global : Core.Global}
    (globalAt : module.globals[index]? = some global) :
    let func := (lowerGlobal module global).init
    InstructionRootsClosed (resultRoots (lower module) (lower module).implTypes)
      (func.valueTypes (lower module)) func
      (func.provenance (resultRoots (lower module) (lower module).implTypes)
        (func.valueTypes (lower module)) (lower module).rootCount) := by
  apply instructionRootsClosed_of_quiet
  rw [lowerGlobal_provenance_fixed accepted globalAt]

#print axioms lowerContextAt_provenance_base_bounds
#print axioms lowerGlobal_provenance_base_bounds
#print axioms accepted_function_provenance_fixed
#print axioms lowerContextAt_provenance_fixed
#print axioms accepted_resultRoots_global_bounds
#print axioms lowerGlobal_provenance_fixed
#print axioms accepted_function_instructionRootsClosed
#print axioms lowerContextAt_instructionRootsClosed
#print axioms lowerGlobal_instructionRootsClosed

end Goose.Lower.Validation

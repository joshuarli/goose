import Goose.Lower.Validation.SourceSymbolAnnotationFacts
import Goose.Lower.Validation.SourceCanonicalRootFloorsBounds

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem valueRootRows_root_bounds {env : PEnv} {table : SourceRootTable}
    {recipes : Array (ValueId × ScopeId)}
    (bounded : SourceCanonicalRootFloors.SourceTableBounds env.mod env.impl table)
    {value : ValueId} {roots : List RootRef}
    (member : (value, roots) ∈ (lowerValueRootRows env table recipes).getD #[]) :
    ∀ root ∈ roots,
      match root with
      | .local index => index < env.impl.vars.size
      | .global index => index < env.mod.globals.size
      | .param index => index < env.impl.params.size := by
  obtain ⟨scope, _, rfl⟩ := SourceCanonicalRootFloors.lowerValueRootRows_source env table recipes member
  exact lowerContextRootCeiling_root_bounds (bounded.getD scope)

theorem lowerContextAt_symbol_tables {module : Core.Module} {contextIndex : ContextId}
    {ctx : Core.Context} {impl : Core.Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some ctx)
    (implAt : module.impls[ctx.impl]? = some impl) :
    SymbolTableFacts (lower module) (lowerContextAt module ctx impl) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have positive := lowerImpl_blocks_nonempty module impl
    simpa only [Array.isEmpty, lowerContextAt, Nat.ne_of_gt positive, decide_false] using Bool.false_eq_false
  · intro index parent row
    exact lowerImpl_scopeParents_of_accepted accepted implAt index parent row
  · exact lowerImpl_slot_scopes accepted implAt
  · exact fun index row => lowerImpl_function_origin accepted implAt row
  · intro summary known target member
    exact lowerImpl_summaryTarget_bounds accepted implAt known target member
  · simp [lowerContextAt, lowerContextRootInfo, lowerImpl, lowerImplFromState]
  · exact lowerContextAt_parameter_facts accepted contextAt implAt
  · exact lowerContextAt_content_facts accepted contextAt implAt
  · exact lowerContextAt_result_facts accepted contextAt implAt
  · intro slot roots member
    obtain ⟨found, foundAt, context⟩ := (validate_modOk module accepted).ctx contextIndex ctx contextAt
    rw [implAt] at foundAt
    cases foundAt
    change (slot, roots) ∈ (ctx.varRoots.filterMap fun (slot, roots) =>
      match impl.vars[slot]? with
      | some localVar => if !localVar.ty.isRefLike then none
          else some (slot, if localVar.ty.isRefSlice &&
            (impl.params[slot]?).any (fun parameter => parameter.var == slot) then [.param slot]
            else lowerContextRootCeiling ctx impl roots)
      | none => none).toArray.toList at member
    simp only at member
    obtain ⟨⟨sourceSlot, sourceRoots⟩, annotation, selected⟩ := List.mem_filterMap.mp member
    cases present : impl.vars[sourceSlot]? with
    | none => simp [present] at selected
    | some localVar =>
      simp only [present] at selected
      split at selected
      · simp at selected
      · simp only [Option.some.injEq, Prod.mk.injEq] at selected
        obtain ⟨rfl, rfl⟩ := selected
        have slotBound := (Array.getElem?_eq_some_iff.mp present).1
        constructor
        · simpa [lowerContextAt, lowerImpl, lowerImplFromState, lowerEnv] using slotBound
        · intro root rootMember
          split at rootMember
          · have reference : localVar.ty.isRefSlice = true := by
              simp_all only [Bool.and_eq_true]
            obtain ⟨param, parameter, _, _⟩ := SummaryPreservation.accepted_refSlice_parameter
              accepted implAt present reference
            have parameterBound := (Array.getElem?_eq_some_iff.mp parameter).1
            simp only [List.mem_singleton] at rootMember
            subst root
            simpa [lowerContextAt, lowerImpl, lowerImplFromState] using parameterBound
          · have bound := lowerContextRootCeiling_root_bounds
              (checkAnnotationShape_root_bounds context.annotationShape annotation) root rootMember
            cases root <;> simpa [lower, lowerContextAt, lowerImpl, lowerImplFromState, lowerEnv] using bound

  · intro value roots member
    constructor
    · exact SourceCanonicalRootFloors.lowerContextAt_valueRoots_numValues module ctx impl
        (lowerContextAt_state_numValues module ctx impl) member
    · have bounded := SourceCanonicalRootFloors.lowerContext_source_table_bounds accepted contextAt implAt
      have rootBounds := valueRootRows_root_bounds (env := ⟨module, impl, ctx, []⟩) bounded
        (Array.mem_toList_iff.mp member)
      intro root rootMember
      have bound := rootBounds root rootMember
      cases root <;> simpa [lower, lowerContextAt, lowerImpl, lowerImplFromState, lowerEnv] using bound
  · exact SourceCanonicalRootFloors.lowerContextAt_valueRootKeys module ctx impl

theorem lowerGlobal_symbol_tables {module : Core.Module} {index : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ()) (lookup : module.globals[index]? = some global) :
    SymbolTableFacts (lower module) (lowerGlobal module global).init := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have positive := lowerGlobal_blocks_nonempty module global
    simp only [Array.isEmpty, Nat.ne_of_gt positive, decide_false]
  · intro scope parent row
    exact lowerGlobal_scopeParents_of_accepted accepted lookup scope parent row
  · simp [lowerGlobal]
  · exact fun origin row => lowerGlobal_function_origin accepted lookup row
  · simp [lowerGlobal]
  · rfl
  · simp [lowerGlobal]
  · simp [lowerGlobal]
  · simp [lowerGlobal]
  · simp [lowerGlobal]

  · intro value roots member
    constructor
    · exact SourceCanonicalRootFloors.lowerGlobal_valueRoots_numValues module global
        (lowerGlobal_state_numValues module global) member
    · have bounded := SourceCanonicalRootFloors.lowerGlobal_source_table_bounds accepted lookup
      have rootBounds := valueRootRows_root_bounds (env := ⟨module, initImpl, initContext, []⟩) bounded
        (Array.mem_toList_iff.mp member)
      intro root rootMember
      have bound := rootBounds root rootMember
      cases root <;> simpa [lower, lowerGlobal, initImpl] using bound
  · exact SourceCanonicalRootFloors.lowerGlobal_valueRootKeys module global

theorem lowerContextAt_checkSymbols_of_references {module : Core.Module} {contextIndex : ContextId}
    {ctx : Core.Context} {impl : Core.Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some ctx)
    (implAt : module.impls[ctx.impl]? = some impl)
    (references : ∀ block ∈ (lowerContextAt module ctx impl).blocks.toList, ∀ inst ∈ block.insts,
      Inst.SymbolsWithin (lowerEnv module impl.vars impl.results.toList)
        (lowerContextAt module ctx impl).scopes.size (lowerContextAt module ctx impl).numValues
        (lowerContextAt module ctx impl).blocks.size inst) (label : String) :
    checkSymbols (lower module) label (lowerContextAt module ctx impl) = .ok () := by
  apply checkSymbols_of_tables (lowerContextAt_symbol_tables accepted contextAt implAt)
    (lowerImpl_dense_definitions module impl) references
  all_goals simp [lowerEnv, lower, lowerContextAt, lowerImpl, lowerImplFromState]

theorem lowerGlobal_checkSymbols_of_references {module : Core.Module} {index : GlobalId}
    {global : Core.Global} (accepted : Core.validate module = .ok ())
    (lookup : module.globals[index]? = some global)
    (references : ∀ block ∈ (lowerGlobal module global).init.blocks.toList, ∀ inst ∈ block.insts,
      Inst.SymbolsWithin (lowerEnv module #[] [global.ty]) (lowerGlobal module global).init.scopes.size
        (lowerGlobal module global).init.numValues (lowerGlobal module global).init.blocks.size inst)
    (label : String) : checkSymbols (lower module) label (lowerGlobal module global).init = .ok () := by
  apply checkSymbols_of_tables (lowerGlobal_symbol_tables accepted lookup)
    (lowerGlobal_dense_definitions module global) references
  all_goals simp [lowerEnv, lower, lowerGlobal]

end Goose.Lower.Validation

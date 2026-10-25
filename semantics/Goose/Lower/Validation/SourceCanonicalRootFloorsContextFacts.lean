import Goose.Lower.Validation.SourceCanonicalRootFloorsFacts
import Goose.Lower.Validation.ReplacementContentFlowSourceSeedFloors
import Goose.Lower.Validation.ProvenanceSourceAccepted
import Goose.Lower.Validation.ValidationTypedModuleDefinitions
import Goose.Lower.Validation.SummaryPreservationParameters

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.Core.Sound Goose.GIR ProvenanceConvergence

private theorem annotation_member {rows : List (Nat × List RootRef)} {index : Nat}
    {roots : List RootRef} (query : (rows.find? (·.1 == index)).map (·.2) = some roots) :
    (index, roots) ∈ rows := by
  cases found : rows.find? (·.1 == index) with
  | none => simp [found] at query
  | some row =>
      have key : row.1 = index := eq_of_beq
        (List.find?_some (p := fun candidate : Nat × List RootRef => candidate.1 == index) (a := row) found)
      have value : row.2 = roots := by simpa only [found, Option.map_some, Option.some.injEq] using query
      simpa only [← key, ← value] using List.mem_of_find?_eq_some found

theorem sourceCanonicalTables_context {module : Core.Module} {context : Context} {impl : Impl}
    {index : ContextId} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl) (scopes : List ScopeId) :
    SourceCanonicalTables ⟨module, impl, context, scopes⟩ (lowerContextAt module context impl) := by
  have moduleOk := validate_modOk module accepted
  have contextOk : CtxOk module impl context := by
    obtain ⟨other, otherAt, checked⟩ := moduleOk.ctx index context contextAt
    rw [implAt] at otherAt
    cases otherAt
    exact checked
  have implOk := moduleOk.impl context.impl impl implAt
  have functionAt := lower_func_at contextAt implAt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((lowerContextAt_provenance_base_bounds accepted contextAt implAt).with_results
      (module := lower module) (accepted_resultRoots_global_bounds accepted)).finite
  · exact finiteRootUniverse_le_module
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? functionAt))
  · intro block member value op definition
    exact lowerContext_definition_typed_of_accepted accepted implAt member definition
  · intro block member value op definition
    have dense := dense_finishBlocks (lowerImplState_denseDefinitions module impl)
      (func := lowerContextAt module context impl) rfl
    exact native_definition_bounded dense member definition
  · intro value roots row
    exact lowerContextAt_valueRoots_numValues module context impl
      (lowerContextAt_state_numValues module context impl) (Array.mem_toList_iff.mpr row)
  · intro slot localVar row
    refine ⟨⟨localVar.ty, localVar.kind, localVar.scope, slot⟩, ?_, rfl⟩
    simp [lowerContextAt, lowerImpl, lowerImplFromState, lowerEnv, Array.getElem?_mapIdx, row]
  · intro slot localVar row reference ordinary
    change ((context.varRoots.find? (·.1 == slot)).map (·.2)).getD [] ⊆ _
    cases found : context.varRoots.find? (·.1 == slot) with
    | none => simp
    | some annotation =>
        have key : annotation.1 = slot := eq_of_beq
          (List.find?_some (p := fun candidate : Nat × List RootRef => candidate.1 == slot)
            (a := annotation) found)
        have member : (slot, annotation.2) ∈ context.varRoots := by
          simpa only [← key] using List.mem_of_find?_eq_some found
        simp only [Option.map_some, Option.getD_some]
        exact ReplacementContentFlowSource.lowerContext_slot_seed_source row reference ordinary member
  · intro slot roots query
    have query' : (context.contentRoots.find? (·.1 == slot)).map (·.2) = some roots := query
    obtain ⟨parameterBound, annotation, _⟩ := contextOk.content slot roots query'
    obtain ⟨param, parameterAt⟩ : ∃ param, impl.params[slot]? = some param :=
      ⟨impl.params[slot], by simp [parameterBound]⟩
    have aligned := (implOk.params slot param parameterAt).1
    obtain ⟨_, localVar, variableAt, reference, _, _⟩ :=
      Core.Declarative.declaredContents_sound module impl context contextOk.contentShape slot roots
        (annotation_member query')
    refine ⟨localVar.ty, ?_, reference, ?_, ?_⟩
    · simp [lowerContextAt, lowerImpl, lowerImplFromState, List.getElem?_map,
        Array.getElem?_toList, parameterAt, tyOfVar, aligned, variableAt]
    · exact ReplacementContentFlowSource.lowerContext_slot_seed_parameter variableAt reference
        parameterAt aligned (annotation_member annotation)
    · have rendered := SummaryPreservation.lowerContextRootInfo_contents_eq parameterAt
        (by simpa only [aligned] using query')
      change roots ⊆ (((lowerContextRootInfo context impl).contents.find?
        (·.1 == slot)).map (·.2)).getD []
      simp only [rendered, Option.map_some, Option.getD_some]
      exact fun _ member => member
  · intro callee called calledImpl calledAt calledImplAt type single reference
    exact lowerContext_resultRoots_declared_floor calledAt calledImplAt single reference

end Goose.Lower.Validation.SourceCanonicalRootFloors

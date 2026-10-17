import Goose.Lower.Validation.SourceCanonicalRootFloorsContextFacts

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR ProvenanceConvergence

theorem sourceCanonicalTables_global {module : Core.Module} {global : Core.Global}
    {index : GlobalId} (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[index]? = some global) (scopes : List ScopeId) :
    SourceCanonicalTables ⟨module, initImpl, initContext, scopes⟩ (lowerGlobal module global).init := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((lowerGlobal_provenance_base_bounds accepted globalAt).with_results
      (module := lower module) (accepted_resultRoots_global_bounds accepted)).finite
  · rw [finiteRootUniverse_length]
    simp only [lowerGlobal, List.length_nil, Array.size_empty, Nat.add_zero]
    unfold GIR.Module.rootCount
    omega
  · intro block member value op definition
    exact lowerGlobal_definition_typed_of_accepted accepted globalAt member definition
  · intro block member value op definition
    exact native_definition_bounded (lowerGlobal_dense_definitions module global) member definition
  · intro value roots row
    exact lowerGlobal_valueRoots_numValues module global
      (lowerGlobal_state_numValues module global) (Array.mem_toList_iff.mpr row)
  · intro slot localVar row
    simp [initImpl] at row
  · intro slot localVar row
    simp [initImpl] at row
  · intro slot roots query
    simp [PEnv.cont, initContext] at query
  · intro callee called calledImpl calledAt calledImplAt type single reference
    exact lowerContext_resultRoots_declared_floor calledAt calledImplAt single reference

end Goose.Lower.Validation.SourceCanonicalRootFloors

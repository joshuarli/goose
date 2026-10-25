import Goose.Lower.Validation.ReplacementContentFlowSourceReadyCallees

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem checkReturned_of_initial_extends {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {state : State}
    (canonical : state.CanonicalWithin func types provenance)
    (parameters : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (growth : (start func types).Extends state)
    (shape : func.results = [] ∨ ∃ type, func.results = [type])
    (rows : ∀ type, func.results = [type] → type.isRefLike = true →
      ∃ roots, func.roots.results[0]? = some roots) :
    checkReturned func state = true := by
  rcases shape with empty | ⟨type, single⟩
  · simp [checkReturned, empty]
  · by_cases reference : type.isRefLike = true
    · obtain ⟨declared, row⟩ := rows type single reference
      obtain ⟨actual, known, bound⟩ := (canonical.returned type single reference).actual parameters
        (returned_ready_of_initial_extends growth)
      rw [row] at bound
      simp only [Option.getD_some] at bound
      simp only [checkReturned, single, reference, ↓reduceIte, row, Option.any_some, rootsWithin, known,
        Option.any_some]
      exact List.all_eq_true.mpr (fun root member => List.contains_iff_mem.mpr (bound member))
    · simp [checkReturned, single, reference]

theorem checkReturned_of_canonical {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {state : State}
    (canonical : state.CanonicalWithin func types provenance)
    (parameters : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (reachable : FunctionReachable module callees func types (start func types) state)
    (shape : func.results = [] ∨ ∃ type, func.results = [type])
    (rows : ∀ type, func.results = [type] → type.isRefLike = true →
      ∃ roots, func.roots.results[0]? = some roots) :
    checkReturned func state = true :=
  checkReturned_of_initial_extends canonical parameters reachable.extends shape rows

#print axioms checkReturned_of_initial_extends

#print axioms checkReturned_of_canonical

end Goose.Lower.Validation.ReplacementContentFlowSource
